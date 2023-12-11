package main

import (
	"fmt"
	"time"
)

func main(){
	t1 := float64(time.Time.UnixNano(time.Now())) / 1000000
	time.Sleep(time.Second * 3)
	t2 := float64(time.Time.UnixNano(time.Now())) / 1000000
	fmt.Println(t2 - t1)
}