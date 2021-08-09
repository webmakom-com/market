package storage

import (
	"bytes"
	"encoding/json"
	"fmt"
	"github.com/tkanos/gonfig"
	"io/ioutil"
	"net/http"
	"os"
	"path/filepath"
	"time"
)

type Token struct {
	Id    string `json:"_id"`
	Token string `json:"token"`
}

type Login struct {
	email    string
	password string
}

type Request struct {
	login        Login
	Collection   string
	SelectString interface{}
	Options      string
	token        string
	Data         interface{}
}

type DatabaseConfig struct {
	Username string `json:"username"`
	Password string `json:"password"`
	Database string `json:"database"`
}

type MongoConfig struct {
	Config  DatabaseConfig `json:"config"`
	Host    string         `json:"host"`
	Enabled bool           `json:"enabled"`
}

type DBConfig struct {
	Local MongoConfig `json:"local"`
}

type SuperAdminConfig struct {
	Email    string `json:"email"`
	Password string `json:"password"`
}

type AuthConfig struct {
	Enabled		bool             `json:"enabled"`
	SuperAdmin	SuperAdminConfig `json:"super_admin"`
}

type Configuration struct {
	DB		DBConfig	`json:"db"`
	Auth	AuthConfig	`json:"auth"`
}

var config Configuration
var myToken Token

func (s Request) toJson() ([]byte, error) {
	if (Login{}) != s.login {
		return json.Marshal(map[string]interface{}{"email": s.login.email, "password": s.login.password})
	}

	if s.SelectString != nil {
		return json.Marshal(map[string]interface{}{"collection": s.Collection, "select": s.SelectString, "token": s.token, "data": s.Data})
	}

	return json.Marshal(map[string]interface{}{"collection": s.Collection, "token": s.token, "data": s.Data})
}

func login() {
	request := Request{login: Login{email: config.Auth.SuperAdmin.Email, password: config.Auth.SuperAdmin.Password}}
	token := CallSaiStorage("login", request)

	_ = json.Unmarshal([]byte(token), &myToken)
}

func CallSaiStorage(method string, request Request) string {
	dir, err := filepath.Abs(filepath.Dir(os.Args[0]))

	if err != nil {
		fmt.Println(err)
	}

	configErr := gonfig.GetConf(dir + "/storage/config.json", &config)

	if configErr != nil {
		fmt.Println("Config missed!! ")
		panic(configErr)
	}

	if method != "login" && myToken.Token == "" {
		login()
	}

	request.token = myToken.Token

	return callSaiStorage("http://localhost:8818/"+method, request)
}

func callSaiStorage(url string, request Request) string {
	jsonStr, jsonErr := request.toJson()
	fmt.Println(string(jsonStr))

	if jsonErr != nil {
		fmt.Println(jsonErr)
		panic(jsonErr)
	}

	req, err := http.NewRequest("POST", url, bytes.NewBuffer(jsonStr))
	req.Header.Set("Content-Type", "application/json")

	client := &http.Client{}
	resp, err := client.Do(req)
	if err != nil {
		fmt.Println(err)
		panic(err)
	}
	defer resp.Body.Close()
	_ = time.AfterFunc(5*time.Second, func() {
		resp.Body.Close()
	})
	body, _ := ioutil.ReadAll(resp.Body)
	return string(body)
}
