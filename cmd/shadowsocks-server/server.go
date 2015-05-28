package main

import (
	"encoding/binary"
	"errors"
	"flag"
	"fmt"
	ss "github.com/shadowsocks/shadowsocks-go/shadowsocks"
	"io"
	"log"
	"net"
	"os"
	"os/signal"
	"runtime"
	"strconv"
	"sync"
	"syscall"
)

import (
	"github.com/codegangsta/negroni"
	//"github.com/phyber/negroni-gzip/gzip"
	"github.com/goincremental/negroni-sessions"
	"github.com/goincremental/negroni-sessions/cookiestore"
	"net/http"
	"encoding/json"
	
    "math/rand"
	
	"io/ioutil"
	"time"
	
	"html/template"
)


var debug ss.DebugLog

const dnsGoroutineNum = 64

func getRequest(conn *ss.Conn) (host string, extra []byte, err error) {
	const (
		idType  = 0 // address type index
		idIP0   = 1 // ip addres start index
		idDmLen = 1 // domain address length index
		idDm0   = 2 // domain address start index

		typeIPv4 = 1 // type is ipv4 address
		typeDm   = 3 // type is domain address
		typeIPv6 = 4 // type is ipv6 address

		lenIPv4   = 1 + net.IPv4len + 2 // 1addrType + ipv4 + 2port
		lenIPv6   = 1 + net.IPv6len + 2 // 1addrType + ipv6 + 2port
		lenDmBase = 1 + 1 + 2           // 1addrType + 1addrLen + 2port, plus addrLen
	)

	// buf size should at least have the same size with the largest possible
	// request size (when addrType is 3, domain name has at most 256 bytes)
	// 1(addrType) + 1(lenByte) + 256(max length address) + 2(port)
	buf := make([]byte, 260)
	var n int
	// read till we get possible domain length field
	ss.SetReadTimeout(conn)
	if n, err = io.ReadAtLeast(conn, buf, idDmLen+1); err != nil {
		return
	}

	reqLen := -1
	switch buf[idType] {
	case typeIPv4:
		reqLen = lenIPv4
	case typeIPv6:
		reqLen = lenIPv6
	case typeDm:
		reqLen = int(buf[idDmLen]) + lenDmBase
	default:
		err = fmt.Errorf("addr type %d not supported", buf[idType])
		return
	}

	if n < reqLen { // rare case
		ss.SetReadTimeout(conn)
		if _, err = io.ReadFull(conn, buf[n:reqLen]); err != nil {
			return
		}
	} else if n > reqLen {
		// it's possible to read more than just the request head
		extra = buf[reqLen:n]
	}

	// Return string for typeIP is not most efficient, but browsers (Chrome,
	// Safari, Firefox) all seems using typeDm exclusively. So this is not a
	// big problem.
	switch buf[idType] {
	case typeIPv4:
		host = net.IP(buf[idIP0 : idIP0+net.IPv4len]).String()
	case typeIPv6:
		host = net.IP(buf[idIP0 : idIP0+net.IPv6len]).String()
	case typeDm:
		host = string(buf[idDm0 : idDm0+buf[idDmLen]])
	}
	// parse port
	port := binary.BigEndian.Uint16(buf[reqLen-2 : reqLen])
	host = net.JoinHostPort(host, strconv.Itoa(int(port)))
	return
}

const logCntDelta = 100

var connCnt int
var nextLogConnCnt int = logCntDelta

func handleConnection(conn *ss.Conn) {
	var host string

	connCnt++ // this maybe not accurate, but should be enough
	if connCnt-nextLogConnCnt >= 0 {
		// XXX There's no xadd in the atomic package, so it's difficult to log
		// the message only once with low cost. Also note nextLogConnCnt maybe
		// added twice for current peak connection number level.
		log.Printf("Number of client connections reaches %d\n", nextLogConnCnt)
		nextLogConnCnt += logCntDelta
	}

	// function arguments are always evaluated, so surround debug statement
	// with if statement
	if debug {
		debug.Printf("new client %s->%s\n", conn.RemoteAddr().String(), conn.LocalAddr())
	}
	closed := false
	defer func() {
		if debug {
			debug.Printf("closed pipe %s<->%s\n", conn.RemoteAddr(), host)
		}
		connCnt--
		if !closed {
			conn.Close()
		}
	}()

	host, extra, err := getRequest(conn)
	if err != nil {
		log.Println("error getting request", conn.RemoteAddr(), conn.LocalAddr(), err)
		return
	}
	debug.Println("connecting", host)
	remote, err := net.Dial("tcp", host)
	if err != nil {
		if ne, ok := err.(*net.OpError); ok && (ne.Err == syscall.EMFILE || ne.Err == syscall.ENFILE) {
			// log too many open file error
			// EMFILE is process reaches open file limits, ENFILE is system limit
			log.Println("dial error:", err)
		} else {
			log.Println("error connecting to:", host, err)
		}
		return
	}
	defer func() {
		if !closed {
			remote.Close()
		}
	}()
	// write extra bytes read from
	if extra != nil {
		// debug.Println("getRequest read extra data, writing to remote, len", len(extra))
		if _, err = remote.Write(extra); err != nil {
			debug.Println("write request extra error:", err)
			return
		}
	}
	if debug {
		debug.Printf("piping %s<->%s", conn.RemoteAddr(), host)
	}
	go ss.PipeThenClose(conn, remote, ss.SET_TIMEOUT)
	ss.PipeThenClose(remote, conn, ss.NO_TIMEOUT)
	closed = true
	return
}

type PortListener struct {
	password string
	listener net.Listener
}

type PasswdManager struct {
	sync.Mutex
	portListener map[string]*PortListener
}

func (pm *PasswdManager) add(port, password string, listener net.Listener) {
	pm.Lock()
	pm.portListener[port] = &PortListener{password, listener}
	pm.Unlock()
}

func (pm *PasswdManager) get(port string) (pl *PortListener, ok bool) {
	pm.Lock()
	pl, ok = pm.portListener[port]
	pm.Unlock()
	return
}

func (pm *PasswdManager) del(port string) {
	pl, ok := pm.get(port)
	if !ok {
		return
	}
	pl.listener.Close()
	pm.Lock()
	delete(pm.portListener, port)
	pm.Unlock()
}

// Update port password would first close a port and restart listening on that
// port. A different approach would be directly change the password used by
// that port, but that requires **sharing** password between the port listener
// and password manager.
func (pm *PasswdManager) updatePortPasswd(port, password string) {
	pl, ok := pm.get(port)
	if !ok {
		log.Printf("new port %s added\n", port)
	} else {
		if pl.password == password {
			return
		}
		log.Printf("closing port %s to update password\n", port)
		pl.listener.Close()
	}
	// run will add the new port listener to passwdManager.
	// So there maybe concurrent access to passwdManager and we need lock to protect it.
	go run(port, password)
}

var passwdManager = PasswdManager{portListener: map[string]*PortListener{}}

func updatePasswd() {
	log.Println("updating password")
	newconfig, err := ss.ParseConfig(configFile)
	if err != nil {
		log.Printf("error parsing config file %s to update password: %v\n", configFile, err)
		return
	}
	oldconfig := config
	config = newconfig

	if err = unifyPortPassword(config); err != nil {
		return
	}
	for port, passwd := range config.PortPassword {
		passwdManager.updatePortPasswd(port, passwd)
		if oldconfig.PortPassword != nil {
			delete(oldconfig.PortPassword, port)
		}
	}
	// port password still left in the old config should be closed
	for port, _ := range oldconfig.PortPassword {
		log.Printf("closing port %s as it's deleted\n", port)
		passwdManager.del(port)
	}
	log.Println("password updated")
}

func waitSignal() {
	var sigChan = make(chan os.Signal, 1)
	signal.Notify(sigChan, syscall.SIGHUP)
	for sig := range sigChan {
		if sig == syscall.SIGHUP {
			updatePasswd()
		} else {
			// is this going to happen?
			log.Printf("caught signal %v, exit", sig)
			os.Exit(0)
		}
	}
}

func run(port, password string) {
	
	var addr string
	var lastTime int64
	
	ln, err := net.Listen("tcp", ":"+port)
	if err != nil {
		log.Printf("error listening port %v: %v\n", port, err)
		return
	}
	passwdManager.add(port, password, ln)
	var cipher *ss.Cipher
	log.Printf("server listening port %v ...\n", port)
	for {
		conn, err := ln.Accept()
		if err != nil {
			// listener maybe closed to update password
			debug.Printf("accept error: %v\n", err)
			return
		}
		
		newaddr := conn.RemoteAddr().String()
		nowtime := time.Now().Unix()
		if addr != newaddr && lastTime >= nowtime {
			conn.Close()
			continue
		}
		lastTime = nowtime
		addr = newaddr
		
		// Creating cipher upon first connection.
		if cipher == nil {
			log.Println("creating cipher for port:", port)
			cipher, err = ss.NewCipher(config.Method, password)
			if err != nil {
				log.Printf("Error generating cipher for port: %s %v\n", port, err)
				conn.Close()
				continue
			}
		}
		go handleConnection(ss.NewConn(conn, cipher.Copy()))
	}
}

func enoughOptions(config *ss.Config) bool {
	return config.ServerPort != 0 && config.Password != ""
}

func unifyPortPassword(config *ss.Config) (err error) {
	if len(config.PortPassword) == 0 { // this handles both nil PortPassword and empty one
		if !enoughOptions(config) {
			fmt.Fprintln(os.Stderr, "must specify both port and password")
			return errors.New("not enough options")
		}
		port := strconv.Itoa(config.ServerPort)
		config.PortPassword = map[string]string{port: config.Password}
	} else {
		if config.Password != "" || config.ServerPort != 0 {
			fmt.Fprintln(os.Stderr, "given port_password, ignore server_port and password option")
		}
	}
	return
}

var configFile string
var config *ss.Config

func main() {
	log.SetFlags(log.Ldate | log.Ltime | log.Lshortfile)
	log.SetOutput(os.Stdout)

	var cmdConfig ss.Config
	var printVer bool
	var core int

	flag.BoolVar(&printVer, "version", false, "print version")
	flag.StringVar(&configFile, "c", "config.json", "specify config file")
	flag.StringVar(&cmdConfig.Password, "k", "", "password")
	flag.IntVar(&cmdConfig.ServerPort, "p", 0, "server port")
	flag.IntVar(&cmdConfig.Timeout, "t", 60, "connection timeout (in seconds)")
	flag.StringVar(&cmdConfig.Method, "m", "", "encryption method, default: aes-256-cfb")
	flag.IntVar(&core, "core", 0, "maximum number of CPU cores to use, default is determinied by Go runtime")
	flag.BoolVar((*bool)(&debug), "d", false, "print debug message")

	flag.Parse()

	if printVer {
		ss.PrintVersion()
		os.Exit(0)
	}

	ss.SetDebug(debug)

	var err error
	config, err = ss.ParseConfig(configFile)
	if err != nil {
		if !os.IsNotExist(err) {
			fmt.Fprintf(os.Stderr, "error reading %s: %v\n", configFile, err)
			os.Exit(1)
		}
		config = &cmdConfig
	} else {
		ss.UpdateConfig(config, &cmdConfig)
	}
	if config.Method == "" {
		config.Method = "aes-256-cfb"
	}
	if err = ss.CheckCipherMethod(config.Method); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	if err = unifyPortPassword(config); err != nil {
		os.Exit(1)
	}
	if core > 0 {
		runtime.GOMAXPROCS(core)
	}
	
	initPortMap()
	if runtime.GOOS == "linux"  {
		limitConfig.Init("/etc/limit.json")
	} else {
		limitConfig.Init("limit.json")
	}
	
	
	for port, password := range config.PortPassword {
		go run(port, password)
	}
	
	go runWeb()
	go DaysLimitLoop()

	waitSignal()
}

func atoi(s interface{}) int{
	v,ok := s.(string)
	if ok == false {
		return 0
    }
	i, err := strconv.Atoi(v)
	if err != nil {
		return 0
	}
	return i
}

func SaveStruct(i interface{},path string) (err error) {
	b,err := json.Marshal(i)
	if err == nil {
		err = ioutil.WriteFile(path, b, 0644)
	}
	checkErr(err)
	return
}

var portMap struct {
	sync.Mutex
	ports [1000]bool
	config *ss.Config
}
func initPortMap() {
	portMap.Lock()
	conf, err := ss.ParseConfig(configFile)
	if err == nil {
		
		if conf.ServerPort >= 8000 && conf.ServerPort <= 9000 {
			portMap.ports[conf.ServerPort-8000] = true
		}
		
		for portstr,_ := range conf.PortPassword {
			port := atoi(portstr)
			if port >= 8000 && port <= 9000 {
				portMap.ports[port-8000] = true
			} else {
				log.Println("port overflow!")
			}
		}
		portMap.config = conf
	}
	portMap.Unlock()
	checkErr(err)
}

func getPort() (port int,password string, err error) {
	portMap.Lock()
	for i,val := range portMap.ports {
		if val == false {
			portMap.ports[i] = true
			port = 8000+i
			break
		}
	}
	
	if port != 0 {
		password = RandSeq(8)
		if portMap.config.PortPassword == nil {
			portMap.config.PortPassword = make(map[string]string)
		}
		portMap.config.PortPassword[strconv.Itoa(port)] = password
		err = SaveStruct(portMap.config, configFile)
		if err != nil {
			portMap.ports[port-8000] = false
			port = 0
		}
	} else {
		err = errors.New("getPort error: no spare ports")
	}
	
	portMap.Unlock()
	
	return
}

func freePort(port int) (err error) {
	portMap.Lock()
	if port >= 8000 && port <= 9000 {
		portMap.ports[port-8000] = false
		delete(portMap.config.PortPassword, strconv.Itoa(port))
		err = SaveStruct(portMap.config, configFile)
	} else {
		err = errors.New("port number must in 8000~9000")
	}
	portMap.Unlock()
	passwdManager.del(strconv.Itoa(port))
	
	return
}

type PortConfig struct {
	EndDate string
	Conn int
	LimitIP int `json:"limit_ip"`
	Password string
	Port int
}

type LimitConfig struct {
	sync.Mutex
	Password   string      `json:"password"`
	// following options are only used by server
	PortLimit map[string]*PortConfig `json:"port_limit"`
	filename string
}

var limitConfig = &LimitConfig{PortLimit:make(map[string]*PortConfig),filename:"limit.json"}
func (c *LimitConfig) Init(file string) {
	
	c.Lock()
	
	c.filename = file
	
	b, err := ioutil.ReadFile(file)
	if err == nil {
		json.Unmarshal(b, c)
		if c.PortLimit == nil {
			c.PortLimit = make(map[string]*PortConfig)
		}
	}
	c.Unlock()
	
	checkErr(err)
}

func checkErr(err error) {
	if err != nil {
		log.Println(err)
	}
}

func (c *LimitConfig) Save() error {
	return SaveStruct(c, c.filename)
}

func (c *LimitConfig) Del(port string, save bool) error {
	
	var err error
	
	c.Lock()
	_,ok := c.PortLimit[port]
	if ok == true {
		delete(c.PortLimit, port)
		if save == true {
			err = c.Save()
		}
	} else {
		err = errors.New("port not exist")
	}
	c.Unlock()
	
	checkErr(freePort(atoi(port)))
	
	return err
	
}

func (c *LimitConfig) Add(days int, conn int) (*PortConfig, error) {
	port,password,err := getPort()
	if port == 0 {
		return nil,err
	}
	y,m,d := time.Unix(time.Now().Unix()+int64(days)*24*3600, 0).Date()
	dateStr := fmt.Sprintf("%d-%d-%d", y, m, d)
	pcon := &PortConfig{EndDate:dateStr, Conn:conn, Password:password, Port:port}
	
	c.Lock()
	c.PortLimit[strconv.Itoa(port)] = pcon
	b,err := json.Marshal(c)
	if err == nil {
		err = ioutil.WriteFile(c.filename, b, 0644)
	}
	c.Unlock()
	
	checkErr(err)
	
	if err == nil {
		go run(strconv.Itoa(port), password)
		return pcon,nil
	} else {
		return nil,err
	}
	
}

func runWeb() {
	
	mux := http.NewServeMux()
	mux.HandleFunc("/config", HandleConfig)
	mux.HandleFunc("/", HandleLogin)
	
	n := negroni.Classic()
	store := cookiestore.New([]byte("ss"))
	n.Use(sessions.Sessions("shadow", store))
	//n.Use(gzip.Gzip(gzip.DefaultCompression))
	n.UseHandler(mux)
	n.Run(":3000")
	
}

func RenderLogin(w http.ResponseWriter, param map[string]interface{}) {
	t := template.New("login")
	t, err := t.Parse(`<!DOCTYPE html>
		<html lang="zh-cn">
		<head>
		<meta charset="utf-8">
		<meta http-equiv="X-UA-Compatible" content="IE=edge">
		<meta name="viewport" content="width=device-width, initial-scale=1">
		<title>登陆</title></head>
		<body style="background-color: rgb(221,221,221);"><form  method="get" style="margin-top:100px;text-align:center;"><input type="text" name="pwd" placeholder="密码"/><input type="submit" value="{{.btn_val}}" />{{if .pwd_empty}}<br/>请输入密码{{end}}{{if .pwd_err}}<br/>密码错误{{end}}</form></body>
		</html>`)
	checkErr(err)
	err = t.Execute(w, param)
	checkErr(err)
}

func HandleLogin(w http.ResponseWriter, req *http.Request) {
	
	if req.URL.Path != "/" {
        http.NotFound(w,req)
		return
    }
	
	param := make(map[string]interface{})
	req.ParseForm()
	password, _ := req.Form["pwd"]
	
	limitConfig.Lock()
	pwd := limitConfig.Password
	limitConfig.Unlock()
	
	if password == nil {
		
		if pwd == "" {
			param["btn_val"] = "设置"
		} else {
			param["btn_val"] = "登录"
		}
		
	} else {
		pwd_in := password[0]
		if pwd == "" {
			
			if pwd_in != "" {
				limitConfig.Lock()
				limitConfig.Password = pwd_in
				limitConfig.Save()
				limitConfig.Unlock()
				
				pwdl := len(pwd)
				pwds := pwd
				if pwdl > 1 {
					pwds = pwd[0:pwdl/2]
				}
				session := sessions.GetSession(req)
				session.Set("pwd", pwds)
				
				http.Redirect(w, req, "/config", http.StatusFound)
				return
				
			} else {
				param["btn_val"] = "设置"
				param["pwd_empty"] = true
			}
			
		} else if pwd == pwd_in {
			
			pwdl := len(pwd)
			pwds := pwd
			if pwdl > 1 {
				pwds = pwd[0:pwdl/2]
			}
			session := sessions.GetSession(req)
			session.Set("pwd", pwds)
			
			http.Redirect(w, req, "/config", http.StatusFound)
			
			return
			
		} else {
			param["pwd_err"] = true
		}
		
	}
	
	RenderLogin(w, param)
	
}

func RenderConfig(w http.ResponseWriter, param map[string]interface{}) {
	t := template.New("config")
	t, err := t.Parse(`<!DOCTYPE html>
		<html lang="zh-cn">
		<head>
		<meta charset="utf-8">
		<meta http-equiv="X-UA-Compatible" content="IE=edge">
		<meta name="viewport" content="width=device-width, initial-scale=1">
		<title>config</title></head>
		<body style="background-color: rgb(221,221,221);"><div style="text-align:center;margin:10px;margin-top:100px;"><form method="post"><input type="text" name="days" placeholder="使用天数"/><input type="submit" value="增加"/></form>{{if .add_suc}}{{with .add_suc}}端口：{{.Port}}<br/>密码：{{.Password}}<br/>可使用到：{{.EndDate}}{{end}}{{end}}{{.add_err}}</div><div style="text-align:center;margin:10px;"><form method="post"><input type="text" name="port" placeholder="端口号" /><input type="submit" value="删除"/></form>{{.del_suc}}{{.del_err}}</div></body>
		</html>`)
	checkErr(err)
	err = t.Execute(w, param)
	checkErr(err)

}

func HandleConfig(w http.ResponseWriter, req *http.Request) {
	
	{
		session := sessions.GetSession(req)
		pwdi := session.Get("pwd")
		if pwdi != nil {
			pwd_in := pwdi.(string)
			
			limitConfig.Lock()
			pwd := limitConfig.Password
			limitConfig.Unlock()
			
			if pwd != "" {
				pwdl := len(pwd)
				pwds := pwd
				if pwdl > 1 {
					pwds = pwd[0:pwdl/2]
				}
				if pwds == pwd_in {
					goto session_ok
				}
			}
			
		}
		
		http.Redirect(w, req, "/", http.StatusFound)
		return
	}

session_ok:
	
	if req.Method == "GET" {
		
		RenderConfig(w, nil)
		
	} else {
		
		param := make(map[string]interface{})
		req.ParseForm()
		
		days, _ := req.Form["days"]
		if days != nil {
			
			pcon,err := limitConfig.Add(atoi(days[0]), 0)
			if err == nil {
				
				param["add_suc"] = pcon
				
			} else {
				param["add_err"] = err
			}
		} else {
			//param["add_err"] = "请输入使用多少天"
		}
		
		
		port, _ := req.Form["port"]
		if port != nil {
			
			err := limitConfig.Del(port[0], true)
			if err == nil {
				param["del_suc"] = "删除成功"
				
			} else {
				param["del_err"] = err
			}
		} else {
			//param["del_err"] = "请输入要删除的端口"
		}
		
		RenderConfig(w, param)
			
	}
	
}

var letters = []rune("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ")

func RandSeq(n int) string {
    b := make([]rune, n)
	now := time.Now().Unix()
    for i := range b {
        b[i] = letters[rand.Int63n(now)%int64(len(letters))]
    }
    return string(b)
}

func DaysLimitLoop() {
	
	_,_,day := time.Now().Date()
	for {
		
		nowtime := time.Now()
		_,_,daynew := nowtime.Date()
		if daynew != day {
			day = daynew
			
			limitConfig.Lock()
			for k,v := range limitConfig.PortLimit {
				if v.EndDate != "" {
					var y,m,d int
					fmt.Sscanf(v.EndDate, "%d-%d-%d", &y, &m, &d)
					endDateTime := time.Date(y, time.Month(m), d, 0, 0, 0, 0, nil)
					
					if nowtime.Unix() > endDateTime.Unix()+3600*24 {
						checkErr(limitConfig.Del(k,false))
					}
					
				}
			}
			limitConfig.Save()
			limitConfig.Unlock()
		}
		time.Sleep(20*time.Minute)
	}
	
}


