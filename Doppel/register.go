package main

import (
	"fmt"
	"github.com/aceld/zinx/ziface"
	"github.com/aceld/zinx/znet"
	"os"
	"strconv"
	"time"
	"strings"
	"encoding/json"
	"net/http"
	"go.dedis.ch/kyber/v3/pairing/bn256"
	"go.dedis.ch/kyber/v3/share"
	"go.dedis.ch/kyber/v3/sign/bls"
	"go.dedis.ch/kyber/v3/sign/tbls"
	"go.dedis.ch/kyber/v3"
	"crypto/sha256"
	"sync"
	//"sort"
)

var VIEW = 0
const F = 1
const REGISTER = 0
var RUNNING = false
var ADDRESS = ""
var REPLICAS = map[int]*Replica{}
var NODE_NUM = -1
var REGISTER_ADDRESS = "10.128.0.2:8000"
var PUBKEYS []*share.PubShare
var MY_PRIKEY *share.PriShare
var PUBKEY *share.PubPoly
var MY_PUBKEY *share.PubShare
var PROPOSALS = [2][]*Proposal{}
var mtx1 sync.RWMutex //for REPLICAS
var mtx2 sync.RWMutex //for PROPOSALS
var PARELLEL_PROPOSALS = 0
var TIMER *time.Timer
var TIMEOUT time.Duration = 300000
var TIMEOUT2 time.Duration = 100
var STOP = false
var VIEWCHANGE1 = map[int]*ViewChangeCache{}
var VIEWCHANGE2 = map[int]*ViewChangeCache{}
var VIEWCHANGE3 = map[int]*ViewChangeCache{}
var mtx3 sync.RWMutex //for VIEWCHANGS1
var mtx4 sync.RWMutex //for VIEW
var mtx5 sync.RWMutex //for VIEWCHANGS2
var mtx6 sync.RWMutex //for VIEWCHANGS3
var PARELLEL_PROPOSALS_BACKUP = 0
var VCTIME_START = -1.0
var VCTIME_END = -1.0
var LOAD = 128 * 100
var BDNODES = false
var RECORD = [][]float64{}
var ERROR_PHASE = 1

type Proposal struct{
	Msg *PrePrepareMsg
	Hash [32]byte
	State int
	PrepareMsgs map[int]*SigMsg
	PreCommitMsgs map[int]*SigMsg
	TSigMsg1 *SigMsg
	TSigMsg2 *SigMsg
	Time1 float64
	Time2 float64
}

type ViewChangeCache struct{
	Msgs map[int]*SigMsg
	End bool
}

type Replica struct{
	Address string
	Conn ziface.IClient
}

type RegisterMsg struct{
	SenderId int
	Address string
}

type PrePrepareMsg struct{
	MsgId int
	Data []byte
	Backup int
}

type VoteMsg struct{
	MsgId int
	Phase int
	Hash []byte
	Backup int
}

type SigMsg struct{
	SenderId int
	View int
	Type string
	Data []byte
	Sig []byte
}

type ViewChangeMsg struct{
	Msgs []*SigMsg
	State []int
	Phase int
}

type NilMsg struct{
	Arr []int
	Proof []byte
	Sig []byte
}

func hash(data []byte) []byte{
	hash := sha256.New()
	hash.Write(data)
	return hash.Sum(nil)
}

func reStart(){
	mtx4.Lock()
	VIEW++
	mtx4.Unlock()
	
	time.Sleep(5 * time.Second)
	
	fmt.Println("reStart...")
	
	if NODE_NUM == getLeader(0, 0){
		arr := []float64{}
		for i := 0;i < len(PROPOSALS[0]);i++{
			if PROPOSALS[0][i].Time1 != -1 && PROPOSALS[0][i].Time2 != -1{
				arr = append(arr, PROPOSALS[0][i].Time2 - PROPOSALS[0][i].Time1)
			}else{
				arr = append(arr, -1)
			}
		}
		RECORD = append(RECORD, arr)
		if VCTIME_START != -1 && VCTIME_END != -1{
			RECORD = append(RECORD, []float64{VCTIME_END - VCTIME_START})
		}
	}
	
	if NODE_NUM == getLeader(0, 1){
		arr := []float64{}
		for i := 0;i < len(PROPOSALS[1]);i++{
			if PROPOSALS[1][i].Time1 != -1 && PROPOSALS[1][i].Time2 != -1{
				arr = append(arr, PROPOSALS[1][i].Time2 - PROPOSALS[1][i].Time1)
			}else{
				arr = append(arr, -1)
			}
		}
		RECORD = append(RECORD, arr)
	}
	
	mtx2.Lock()
	PROPOSALS = [2][]*Proposal{}
	mtx2.Unlock()
	
	PARELLEL_PROPOSALS = 0
	PARELLEL_PROPOSALS_BACKUP = 0
	
	mtx3.Lock()
	VIEWCHANGE1 = map[int]*ViewChangeCache{}
	mtx3.Unlock()
	
	mtx5.Lock()
	VIEWCHANGE2 = map[int]*ViewChangeCache{}
	mtx5.Unlock()
	
	mtx6.Lock()
	VIEWCHANGE3 = map[int]*ViewChangeCache{}
	mtx6.Unlock()
	
	mtx4.Lock()
	VIEW = 0
	mtx4.Unlock()
	
	VCTIME_START = -1.0
	VCTIME_END = -1.0
	STOP = false
	
	if NODE_NUM == 0{
		time.Sleep(5 * time.Second)
		RUNNING = true
	}
}

func viewchange2(view, id int){
	time.Sleep(time.Millisecond * TIMEOUT2)
	
	mtx2.Lock()
	if PROPOSALS[0][id].State < 2{
		fmt.Println("backup viewchange2")
		viewChange(view)
	}
	mtx2.Unlock()
}

func viewChange(view int){
	mtx4.Lock()
	if view <= VIEW{
		mtx4.Unlock()
		return
	}
	VIEW = view
	mtx4.Unlock()
	if TIMER != nil{
		TIMER.Stop()
	}
	STOP = true
	RUNNING = false
	
	suite := bn256.NewSuite()
	state := []int{}
	msgs := []*SigMsg{}
	i := 0
	for ;i < len(PROPOSALS[0]);i++{
		if PROPOSALS[0][i].State >= 1{
			msgs = append(msgs, PROPOSALS[0][i].TSigMsg1)
			state = append(state, 0)
		}else if ERROR_PHASE == 1{
			nilArr := []int{view, i, 1}
			nilArrJson, _ := json.Marshal(nilArr)
			nilArrHash := hash([]byte(nilArrJson))
			nilArrSig, _ := tbls.Sign(suite, MY_PRIKEY, nilArrHash)
			nilMsg := NilMsg{nilArr, nil, nilArrSig}
			nilMsgJson, _ := json.Marshal(nilMsg)
			sigMsg := SigMsg{NODE_NUM, view, "Nil1", []byte(nilMsgJson), nil}
			msgs = append(msgs, &sigMsg)
			state = append(state, -1)
		}
	}
	for ;i < len(PROPOSALS[1]);i++{
		/*
		nilArr := []int{view, i, 1}
		nilArrJson, _ := json.Marshal(nilArr)
		nilArrHash := hash([]byte(nilArrJson))
		nilArrSig, _ := tbls.Sign(suite, MY_PRIKEY, nilArrHash)
		nilMsg := NilMsg{nilArr, nil, nilArrSig}
		nilMsgJson, _ := json.Marshal(nilMsg)
		sigMsg := SigMsg{NODE_NUM, view, "Nil1", []byte(nilMsgJson), nil}
		msgs = append(msgs, &sigMsg)
		state = append(state, -1)
		*/
	}
	
	vcMsg := ViewChangeMsg{msgs, state, 1}
	vcMsgJson, _ := json.Marshal(vcMsg)
	vcMsgHash := hash([]byte(vcMsgJson))
	vcMsgSig, _ := tbls.Sign(suite, MY_PRIKEY, vcMsgHash)
	sigMsg := SigMsg{}
	sigMsg = SigMsg{NODE_NUM, view, "ViewChange1", []byte(vcMsgJson), vcMsgSig}
	mtx3.Lock()
	_, ok := VIEWCHANGE1[view]
	if !ok{
		VIEWCHANGE1[view] = &ViewChangeCache{map[int]*SigMsg{}, false}
	}
	VIEWCHANGE1[view].Msgs[NODE_NUM] = &sigMsg
	mtx3.Unlock()
	
	sigMsgJson, _ := json.Marshal(sigMsg)
	bdMsg(6, []byte(sigMsgJson))
}

func timeoutCheck(){
	for ;;{
		select{
			case <- TIMER.C:
				mtx4.Lock()
				VIEW++
				view := VIEW
				mtx4.Unlock()
				fmt.Println("超时, 新Leader ", getLeader(view, 0))
		}
	}
}

func getLeader(num int, backup int) int{
	if backup == 0{
		return (num) % (3 * F + 1)
	}else if backup == 1{
		return (num + 2) % (3 * F + 1)
	}else{
		fmt.Println("backup错误(getLeader)")
		return -1
	}
}

func cryptoInit(){
	n := 3 * F + 1
	t := 2 * F + 1
	suite := bn256.NewSuite()
	coeffs := make([]kyber.Scalar, t)
	for i := 0;i < t;i++{
		coeffs[i]=suite.G2().Scalar().SetInt64(int64(i))
	}
	priPoly := share.CoefficientsToPriPoly(suite.G2(),coeffs)
	pubPoly := priPoly.Commit(suite.G2().Point().Base())
	PUBKEY = pubPoly
	prikeys := priPoly.Shares(n)
	MY_PRIKEY = prikeys[NODE_NUM]
	pubkeys := pubPoly.Shares(n)
	PUBKEYS = pubkeys
	MY_PUBKEY = pubkeys[NODE_NUM]
}

func register(){
	var f = func(conn ziface.IConnection){
		msg := RegisterMsg{NODE_NUM, ADDRESS}
		jsonStr, err := json.Marshal(msg)
		if err != nil {
			fmt.Println("marshal failed!")
			return
		}
		err = conn.SendBuffMsg(10, []byte(strconv.Itoa(NODE_NUM)))
		err = conn.SendBuffMsg(1, []byte(jsonStr))
		if err == nil{
			fmt.Println("注册成功")
		}else{
			fmt.Println("注册失败")
		}
	}
	
	arr := strings.Split(REGISTER_ADDRESS, ":")
	ip := arr[0]
	port, _ := strconv.Atoi(arr[1])
	
	client := znet.NewClient(ip, port)
	REPLICAS[REGISTER] = &Replica{REPLICAS[REGISTER].Address, client}
	client.SetOnConnStart(f)
	client.Start()
}


func mainLoop(){
	data := ""
	for i := 0;i < LOAD;i++{
		data = data + strconv.Itoa(NODE_NUM)
	}
	for ;;{
		mtx4.RLock()
		view := VIEW
		mtx4.RUnlock()
		if RUNNING && (NODE_NUM == getLeader(view, 0) || NODE_NUM == getLeader(view, 1)) && PARELLEL_PROPOSALS < 1{
			backup := -1
			if NODE_NUM == getLeader(view, 0){
				backup = 0
			}else{
				backup = 1
			}
			mtx2.RLock()
			Id := len(PROPOSALS[backup])
			mtx2.RUnlock()
			newPrePrepareMsg := PrePrepareMsg{Id, []byte(data), backup}
			newPrePrepareJson, _ := json.Marshal(newPrePrepareMsg)
			newPrePrepareHash := hash([]byte(newPrePrepareJson))
			suite := bn256.NewSuite()
			newPrePrepareSig, _ := tbls.Sign(suite, MY_PRIKEY, newPrePrepareHash)
			sigMsg := SigMsg{}
			sigMsg = SigMsg{NODE_NUM, view, "PrePrepare", []byte(newPrePrepareJson), newPrePrepareSig}
			sigMsgJson, _ := json.Marshal(sigMsg)
			sigMsgByte := []byte(sigMsgJson)
			
			voteMsg1 := VoteMsg{Id, 1, newPrePrepareHash, backup}
			voteJson1, _ := json.Marshal(voteMsg1)
			voteHash1 := hash([]byte(voteJson1))
			voteSig1, _ := tbls.Sign(suite, MY_PRIKEY, voteHash1)
			prepareMsg := SigMsg{NODE_NUM, view, "Prepare", []byte(voteJson1), voteSig1}
			
			voteMsg2 := VoteMsg{Id, 2, newPrePrepareHash, backup}
			voteJson2, _ := json.Marshal(voteMsg2)
			voteHash2 := hash([]byte(voteJson2))
			voteSig2, _ := tbls.Sign(suite, MY_PRIKEY, voteHash2)
			commitMsg := SigMsg{NODE_NUM, view, "Commit", []byte(voteJson2), voteSig2}
			
			tempArr := [32]byte{}
			copy(tempArr[:], newPrePrepareHash)
			mtx2.Lock()
			nowTime := float64(time.Time.UnixNano(time.Now())) / 1000000
			PROPOSALS[backup] = append(PROPOSALS[backup], &Proposal{&newPrePrepareMsg, tempArr, 0, map[int]*SigMsg{NODE_NUM: &prepareMsg}, map[int]*SigMsg{NODE_NUM: &commitMsg}, nil, nil, nowTime, -1})
			PARELLEL_PROPOSALS++
			
			mtx2.Unlock()
			
			bdMsg(3, sigMsgByte)
			
			Id++
			fmt.Println("发送PrePrepare消息：", newPrePrepareHash)
		}else if NODE_NUM != getLeader(view, 0) && NODE_NUM != getLeader(view, 1){
			RUNNING = false
		}
		time.Sleep(time.Millisecond * 10)
	}
}

func bdNodes(){
	time.Sleep(time.Second * 3)
	
	if NODE_NUM != REGISTER || len(REPLICAS) != 3 * F + 1{
		return
	}
	addresses := make([]string, 3 * F + 1)
	for id, replica := range REPLICAS{
		addresses[id] = replica.Address
	}
	fmt.Println("全体节点的地址为:", addresses)
	jsonStr, _ := json.Marshal(addresses)
	
	var f = func(conn ziface.IConnection){
		conn.SendBuffMsg(10, []byte(strconv.Itoa(NODE_NUM)))
		err := conn.SendBuffMsg(2, []byte(jsonStr))
		if err != nil{
			fmt.Println("注册失败")
		}
	}
	
	for id, replica := range REPLICAS{
		if id != REGISTER{
			fmt.Println("向地址为", replica.Address, "的节点", id, "发送全体节点的地址")
			conn := replica.Conn
			conn.SetOnConnStart(f)
			conn.Start()
		}
	}
}

func bdMsg(router uint32, data []byte){
	for i := 0;i < 3 * F + 1;i++{
		if i != NODE_NUM{
			go sendMsg(i, router, data)
		}
	}
}

func sendMsg(node int, router uint32, data []byte){
	mtx1.RLock()
	err := REPLICAS[node].Conn.Conn().SendBuffMsg(router, data)
	mtx1.RUnlock()
	if err != nil{
		fmt.Println("发送消息失败(sendMsg)", err)
	}
}

type RegisterRouter struct {
	znet.BaseRouter
}

func (r *RegisterRouter) Handle(request ziface.IRequest) {
	jsonStr := string(request.GetData())
	msg := RegisterMsg{}
	err := json.Unmarshal([]byte(jsonStr), &msg)
	if err != nil {
		fmt.Println("unmarshal failed in RegisterRouter!")
		return
	}
	
	fmt.Println("connect from node ", msg.SenderId, " with address ", msg.Address)
	
	arr := strings.Split(msg.Address, ":")
	ip := arr[0]
	port, _ := strconv.Atoi(arr[1])
	client := znet.NewClient(ip, port)
	
	mtx1.Lock()
	REPLICAS[msg.SenderId] = &Replica{msg.Address, client}
	length := len(REPLICAS)
	mtx1.Unlock()
	fmt.Println("目前已有", len(REPLICAS), "个节点完成注册")
	if length == 3 * F + 1{
		bdNodes()
		fmt.Println("全部", len(REPLICAS), "个节点完成注册,可启动协议")
	}
}

type BDNodesRouter struct {
	znet.BaseRouter
}

func (r *BDNodesRouter) Handle(request ziface.IRequest){
	time.Sleep(time.Second * 3)
	jsonStr := string(request.GetData())
	addresses := make([]string, 3 * F + 1)
	err := json.Unmarshal([]byte(jsonStr), &addresses)
	if err != nil {
		fmt.Println("unmarshal failed in BDNodesRouter!")
		return
	}
	fmt.Println("收到Register广播的全部节点地址:", addresses)
	var f = func(conn ziface.IConnection){
		conn.SendBuffMsg(10, []byte(strconv.Itoa(NODE_NUM)))
		err := conn.SendBuffMsg(10, []byte(strconv.Itoa(NODE_NUM)))
		if err != nil{
			fmt.Println("连接失败")
		}
	}
	mtx1.Lock()
	for i := 0;i < len(addresses);i++{
		if i != NODE_NUM && i != REGISTER{
			arr := strings.Split(addresses[i], ":")
			ip := arr[0]
			port, _ := strconv.Atoi(arr[1])
			client := znet.NewClient(ip, port)
			client.SetOnConnStart(f)
			client.Start()
			REPLICAS[i] = &Replica{addresses[i], client}
		}
	}
	mtx1.Unlock()
	time.Sleep(time.Second * 3)
	if !BDNODES{
		bdMsg(10, []byte(strconv.Itoa(NODE_NUM)))
		BDNODES = true
	}
}

type PrePrepareRouter struct {
	znet.BaseRouter
}

func (r *PrePrepareRouter) Handle(request ziface.IRequest){
	mtx4.RLock()
	view := VIEW
	mtx4.RUnlock()
	
	if STOP{
		return
	}
	
	jsonStr := string(request.GetData())
	msg := SigMsg{}
	err := json.Unmarshal([]byte(jsonStr), &msg)
	if err != nil {
		fmt.Println("unmarshal failed in PrePrepareRouter!")
		return
	}
	
	newPrePrepareMsg := PrePrepareMsg{}
	err = json.Unmarshal([]byte(msg.Data), &newPrePrepareMsg)
	if err != nil {
		fmt.Println("unmarshal failed in PrePrepareRouter()!")
		return
	}
	
	if msg.View != view{
		if NODE_NUM == getLeader(msg.View, 1) && newPrePrepareMsg.Backup == 0{
			mtx4.Lock()
			VIEW = msg.View
			view = VIEW
			mtx4.Unlock()
		}else{
			fmt.Println("View错误(PrePrepareRouter)")
			return
		}
	}
	
	if msg.Type != "PrePrepare"{
		fmt.Println("错误的消息类型(PrePrepareRouter)")
		return
	}
	
	suite := bn256.NewSuite()
	hashValue := hash(msg.Data)
	err = bls.Verify(suite, PUBKEYS[msg.SenderId].V, hashValue, msg.Sig[2:])
	if err != nil{
		fmt.Println("签名验证失败(PrePrepareRouter)")
		return
	}
	
	if newPrePrepareMsg.Backup != 0 && newPrePrepareMsg.Backup != 1{
		fmt.Println("Backup错误(PrePrepareRouter)")
		return
	}
	
	if msg.SenderId != getLeader(view, newPrePrepareMsg.Backup){
		fmt.Println("消息发送者的身份错误(PrePrepareRouter)")
		return
	}
	
	mtx2.Lock()
	for newPrePrepareMsg.MsgId >= len(PROPOSALS[newPrePrepareMsg.Backup]){
		PROPOSALS[newPrePrepareMsg.Backup] = append(PROPOSALS[newPrePrepareMsg.Backup], &Proposal{nil, [32]byte{}, -1, map[int]*SigMsg{}, map[int]*SigMsg{}, nil, nil, -1, -1})
	}
		
	if PROPOSALS[newPrePrepareMsg.Backup][newPrePrepareMsg.MsgId].State != -1{
		mtx2.Unlock()
		return
	}else{
		PROPOSALS[newPrePrepareMsg.Backup][newPrePrepareMsg.MsgId].Msg = &newPrePrepareMsg
		PROPOSALS[newPrePrepareMsg.Backup][newPrePrepareMsg.MsgId].State = 0
		tempArr := [32]byte{}
		copy(tempArr[:], hashValue)
		PROPOSALS[newPrePrepareMsg.Backup][newPrePrepareMsg.MsgId].Hash = tempArr
	}
	mtx2.Unlock()
		
	voteMsg := VoteMsg{newPrePrepareMsg.MsgId, 1, hashValue, newPrePrepareMsg.Backup}
	voteJson, _ := json.Marshal(voteMsg)
	voteHash := hash([]byte(voteJson))
	voteSig, _ := tbls.Sign(suite, MY_PRIKEY, voteHash)
	prepareMsg := SigMsg{NODE_NUM, view, "Prepare", []byte(voteJson), voteSig}
	prepareMsgJson, _ := json.Marshal(prepareMsg)
	
	sendMsg(getLeader(view, newPrePrepareMsg.Backup), 4, []byte(prepareMsgJson))
	
	if newPrePrepareMsg.Backup == 0{
		if TIMER == nil{
			TIMER = time.NewTimer(time.Millisecond * TIMEOUT)
			go timeoutCheck()
		}else{
			if !TIMER.Stop() {
				select {
				case <-TIMER.C:
				default:
				}
			}
			TIMER.Reset(time.Millisecond * TIMEOUT)
		}
	}
	
	if NODE_NUM == getLeader(view, 1) && RUNNING == false{
		time.Sleep(10 * time.Millisecond)
		RUNNING = true
	}
}

type PrepareRouter struct {
	znet.BaseRouter
}

func (r *PrepareRouter) Handle(request ziface.IRequest){
	mtx4.RLock()
	view := VIEW
	mtx4.RUnlock()
	
	jsonStr := string(request.GetData())
	msg := SigMsg{}
	err := json.Unmarshal([]byte(jsonStr), &msg)
	if err != nil {
		fmt.Println("unmarshal failed in PrepareRouter!")
		return
	}
	
	prepareMsg := VoteMsg{}
	err = json.Unmarshal(msg.Data, &prepareMsg)
	if err != nil {
		fmt.Println("unmarshal failed in PrepareRouter!")
		return
	}
	
	if prepareMsg.Backup != 0 && prepareMsg.Backup != 1{
		fmt.Println("Backup错误(PrepareRouter)")
		return
	}
	
	if msg.View != view{
		fmt.Println("View错误(PrepareRouter)")
		return
	}
	
	if msg.Type != "Prepare"{
		fmt.Println("错误的消息类型(PrepareRouter)")
		return
	}
	
	suite := bn256.NewSuite()
	hashValue := hash(msg.Data)
	err = bls.Verify(suite, PUBKEYS[msg.SenderId].V, hashValue, msg.Sig[2:])
	if err != nil{
		fmt.Println("签名验证失败(PrepareRouter)")
		return
	}
	
	/********************ONLY FOR TEST!!!!!!!!!!********************/
	if prepareMsg.MsgId == 5 && NODE_NUM == 0 && prepareMsg.Phase == ERROR_PHASE{
		if VCTIME_START == -1{
			VCTIME_START = float64(time.Time.UnixNano(time.Now())) / 1000000
		}
		return
	}
	/********************ONLY FOR TEST!!!!!!!!!!********************/
	
	mtx2.Lock()
	if prepareMsg.MsgId >= len(PROPOSALS[prepareMsg.Backup]){
		fmt.Println("无效的Prepare消息(PrepareRouter)")
		mtx2.Unlock()
		return
	}
	tempArr := [32]byte{}
	copy(tempArr[:], prepareMsg.Hash)
	if tempArr != PROPOSALS[prepareMsg.Backup][prepareMsg.MsgId].Hash{
		fmt.Println("无效的Prepare消息(PrepareRouter)")
		mtx2.Unlock()
		return
	}
	if prepareMsg.Phase == 1{
		if PROPOSALS[prepareMsg.Backup][prepareMsg.MsgId].State < 1{
			PROPOSALS[prepareMsg.Backup][prepareMsg.MsgId].PrepareMsgs[msg.SenderId] = &msg
			if len(PROPOSALS[prepareMsg.Backup][prepareMsg.MsgId].PrepareMsgs) >= 2 * F + 1{
				sigs := make([][]byte, len(PROPOSALS[prepareMsg.Backup][prepareMsg.MsgId].PrepareMsgs))
				i := 0
				for _, msg := range PROPOSALS[prepareMsg.Backup][prepareMsg.MsgId].PrepareMsgs{
					sigs[i] = msg.Sig
					i++
				}
				tSig, _ := tbls.Recover(suite, PUBKEY, hashValue, sigs, 2 * F + 1, 3 * F + 1)
				commitMsg := SigMsg{NODE_NUM, view, "Commit", msg.Data, tSig}
				PROPOSALS[prepareMsg.Backup][prepareMsg.MsgId].TSigMsg1 = &commitMsg
				CommitMsgJson, _ := json.Marshal(commitMsg)
				PROPOSALS[prepareMsg.Backup][prepareMsg.MsgId].State = 1
				/********************ONLY FOR TEST!!!!!!!!!!********************/
				/*
				if prepareMsg.MsgId == 5 && NODE_NUM == 0{
					sendMsg(msg.SenderId, 5, []byte(CommitMsgJson))
				}else{
					bdMsg(5, []byte(CommitMsgJson))
				}
				*/
				/********************ONLY FOR TEST!!!!!!!!!!********************/
				bdMsg(5, []byte(CommitMsgJson))
			}
		}else if view != PROPOSALS[prepareMsg.Backup][prepareMsg.MsgId].TSigMsg1.View{
			commitMsg := SigMsg{NODE_NUM, view, "Commit", PROPOSALS[prepareMsg.Backup][prepareMsg.MsgId].TSigMsg1.Data, PROPOSALS[prepareMsg.Backup][prepareMsg.MsgId].TSigMsg1.Sig}
			commitMsgJson, _ := json.Marshal(commitMsg)
			sendMsg(msg.SenderId, 5, []byte(commitMsgJson))
		}
	}else if prepareMsg.Phase == 2{
		if PROPOSALS[prepareMsg.Backup][prepareMsg.MsgId].State < 2{
			PROPOSALS[prepareMsg.Backup][prepareMsg.MsgId].PreCommitMsgs[msg.SenderId] = &msg
			if len(PROPOSALS[prepareMsg.Backup][prepareMsg.MsgId].PreCommitMsgs) >= 2 * F + 1{
				sigs := make([][]byte, len(PROPOSALS[prepareMsg.Backup][prepareMsg.MsgId].PreCommitMsgs))
				i := 0
				for _, msg := range PROPOSALS[prepareMsg.Backup][prepareMsg.MsgId].PreCommitMsgs{
					sigs[i] = msg.Sig
					i++
				}
				tSig, _ := tbls.Recover(suite, PUBKEY, hashValue, sigs, 2 * F + 1, 3 * F + 1)
				commitMsg := SigMsg{NODE_NUM, view, "Commit", msg.Data, tSig}
				PROPOSALS[prepareMsg.Backup][prepareMsg.MsgId].TSigMsg2 = &commitMsg
				CommitMsgJson, _ := json.Marshal(commitMsg)
				bdMsg(5, []byte(CommitMsgJson))
				PROPOSALS[prepareMsg.Backup][prepareMsg.MsgId].State = 2
				if prepareMsg.Backup == 0{
					PROPOSALS[prepareMsg.Backup][prepareMsg.MsgId].Time2 = float64(time.Time.UnixNano(time.Now())) / 1000000
				}
				PARELLEL_PROPOSALS--
				if prepareMsg.Backup == 1 && (len(PROPOSALS[0]) <= prepareMsg.MsgId || PROPOSALS[0][prepareMsg.MsgId].State < 1){
					fmt.Println("backup viewchange(PrepareRouter)")
					viewChange(view + 1)
				}else if prepareMsg.Backup == 1 && len(PROPOSALS[0]) > prepareMsg.MsgId && PROPOSALS[0][prepareMsg.MsgId].State == 1{
					go viewchange2(view + 1, prepareMsg.MsgId)
				}
			}
		}else if view != PROPOSALS[prepareMsg.Backup][prepareMsg.MsgId].TSigMsg2.View{
			commitMsg := SigMsg{NODE_NUM, view, "Commit", PROPOSALS[prepareMsg.Backup][prepareMsg.MsgId].TSigMsg2.Data, PROPOSALS[prepareMsg.Backup][prepareMsg.MsgId].TSigMsg2.Sig}
			commitMsgJson, _ := json.Marshal(commitMsg)
			sendMsg(msg.SenderId, 5, []byte(commitMsgJson))
		}
	}else{
		fmt.Println("错误的Phase(PrepareRouter)")
		mtx2.Unlock()
		return
	}
	mtx2.Unlock()
}

type CommitRouter struct {
	znet.BaseRouter
}

func (r *CommitRouter) Handle(request ziface.IRequest){
	mtx4.RLock()
	view := VIEW
	mtx4.RUnlock()
	
	if STOP{
		return
	}
	
	jsonStr := string(request.GetData())
	msg := SigMsg{}
	err := json.Unmarshal([]byte(jsonStr), &msg)
	if err != nil {
		fmt.Println("unmarshal failed in CommitRouter!")
		return
	}
	
	commitMsg := VoteMsg{}
	err = json.Unmarshal(msg.Data, &commitMsg)
	if err != nil {
		fmt.Println("unmarshal failed in CommitRouter!")
		return
	}
	
	if commitMsg.Backup != 0 && commitMsg.Backup != 1{
		fmt.Println("Backup错误(PrepareRouter)")
		return
	}
	
	if msg.View != view{
		fmt.Println("View错误(CommitRouter)", msg.View, view)
		return
	}
	
	if msg.Type != "Commit"{
		fmt.Println("错误的消息类型(CommitRouter)")
		return
	}
	
	suite := bn256.NewSuite()
	hashValue := hash(msg.Data)
	err = bls.Verify(suite, PUBKEY.Commit(), hashValue, msg.Sig)
	if err != nil{
		fmt.Println("签名验证失败(CommitRouter)")
		return
	}
	
	if msg.SenderId != getLeader(view, commitMsg.Backup){
		fmt.Println("消息发送者的身份错误(CommitRouter)")
		return
	}
	
	mtx2.Lock()
	for commitMsg.MsgId >= len(PROPOSALS[commitMsg.Backup]){
		PROPOSALS[commitMsg.Backup] = append(PROPOSALS[commitMsg.Backup], &Proposal{nil, [32]byte{}, -1, map[int]*SigMsg{}, map[int]*SigMsg{}, nil, nil, -1, -1})
	}
	if commitMsg.Phase == 1{
		if PROPOSALS[commitMsg.Backup][commitMsg.MsgId].State < commitMsg.Phase{
			PROPOSALS[commitMsg.Backup][commitMsg.MsgId].State = 1
			PROPOSALS[commitMsg.Backup][commitMsg.MsgId].TSigMsg1 = &msg
		}
		voteMsg := VoteMsg{commitMsg.MsgId, 2, commitMsg.Hash, commitMsg.Backup}
		voteJson, _ := json.Marshal(voteMsg)
		voteHash := hash([]byte(voteJson))
		voteSig, _ := tbls.Sign(suite, MY_PRIKEY, voteHash)
		prepareMsg := SigMsg{NODE_NUM, view, "Prepare", []byte(voteJson), voteSig}
		prepareMsgJson, _ := json.Marshal(prepareMsg)
		sendMsg(getLeader(view, commitMsg.Backup), 4, []byte(prepareMsgJson))
	}else{
		if PROPOSALS[commitMsg.Backup][commitMsg.MsgId].State < commitMsg.Phase{
			PROPOSALS[commitMsg.Backup][commitMsg.MsgId].State = 2
			PROPOSALS[commitMsg.Backup][commitMsg.MsgId].TSigMsg2 = &msg
			if commitMsg.Backup == 0{
				PROPOSALS[commitMsg.Backup][commitMsg.MsgId].Time2 = float64(time.Time.UnixNano(time.Now())) / 1000000
			}
		}
		if commitMsg.Backup == 1 && (len(PROPOSALS[0]) <= commitMsg.MsgId || PROPOSALS[0][commitMsg.MsgId].State < 1){
			fmt.Println("backup viewchange(CommitRouter)")
			viewChange(view + 1)
		}else if commitMsg.Backup == 1 && len(PROPOSALS[0]) > commitMsg.MsgId && PROPOSALS[0][commitMsg.MsgId].State == 1{
			go viewchange2(view + 1, commitMsg.MsgId)
		}
	}
	mtx2.Unlock()
}

type ViewChange1Router struct {
	znet.BaseRouter
}

func (r *ViewChange1Router) Handle(request ziface.IRequest){
	mtx4.RLock()
	view := VIEW
	mtx4.RUnlock()
	
	jsonStr := string(request.GetData())
	msg := SigMsg{}
	err := json.Unmarshal([]byte(jsonStr), &msg)
	if err != nil {
		fmt.Println("unmarshal failed in ViewChange1Router!")
		return
	}
	
	suite := bn256.NewSuite()
	hashValue := hash(msg.Data)
	err = bls.Verify(suite, PUBKEYS[msg.SenderId].V, hashValue, msg.Sig[2:])
	if err != nil{
		fmt.Println("签名验证失败1(ViewChange1Router)")
		return
	}
	
	vcMsg := ViewChangeMsg{}
	err = json.Unmarshal(msg.Data, &vcMsg)
	if err != nil {
		fmt.Println("unmarshal failed in ViewChange1Router!")
		return
	}
	
	if msg.View < view{
		fmt.Println("msg.View=", msg.View, "view=", view)
		return
	}
	
	if vcMsg.Phase != 1{
		fmt.Println("Phase错误(ViewChange1Router!)")
		return
	}
	
	
	if len(vcMsg.State) != len(vcMsg.Msgs){
		fmt.Println("长度错误(ViewChange1Router)")
		return
	}
	
	for i := 0;i < len(vcMsg.State);i++{
		if vcMsg.State[i] == 0{
			err = bls.Verify(suite, PUBKEY.Commit(), PROPOSALS[0][i].Hash[0:], vcMsg.Msgs[i].Sig)
			if err != nil{
				fmt.Println("签名验证失败2(ViewChange1Router)")
				return
			}
		}else if vcMsg.State[i] == -1{
			nilMsg := NilMsg{}
			err = json.Unmarshal(vcMsg.Msgs[i].Data, &nilMsg)
			if err != nil {
				fmt.Println("unmarshal failed in ViewChange1Router!")
				return
			}
			arrJson, _ := json.Marshal(nilMsg.Arr)
			hashValue := hash([]byte(arrJson))
			err = bls.Verify(suite, PUBKEYS[vcMsg.Msgs[i].SenderId].V, hashValue, nilMsg.Sig[2:])
			if err != nil{
				fmt.Println("签名验证失败3(ViewChange1Router)")
				return
			}
			if len(nilMsg.Arr) < 3 || nilMsg.Arr[0] != msg.View || nilMsg.Arr[1] != i || nilMsg.Arr[2] != 1{
				fmt.Println("nilMsg错误 ViewChange1Router!")
				return
			}
		}else{
			fmt.Println("state错误(ViewChange1Router)")
			return
		}
	}
	
	mtx3.Lock()
	_, ok := VIEWCHANGE1[msg.View]
	if !ok{
		VIEWCHANGE1[msg.View] = &ViewChangeCache{map[int]*SigMsg{}, false}
	}
	VIEWCHANGE1[msg.View].Msgs[msg.SenderId] = &msg
	
	if !VIEWCHANGE1[msg.View].End && len(VIEWCHANGE1[msg.View].Msgs) == 2 * F + 1{
		if view < msg.View{
			mtx4.Lock()
			VIEW = msg.View
			mtx4.Unlock()
		}
		VIEWCHANGE1[msg.View].End = true
		rev0 := []int{}
		rev1 := []int{}
		msgs0 := []*SigMsg{}
		msgs1 := [][]*SigMsg{}
		for _, v := range VIEWCHANGE1[msg.View].Msgs{
			vcMsg := ViewChangeMsg{}
			json.Unmarshal(v.Data, &vcMsg)
			for i := 0;i < len(vcMsg.State);i++{
				if len(rev0) <= i{
					rev0 = append(rev0, 0)
					rev1 = append(rev1, 0)
					msgs0 = append(msgs0, nil)
					msgs1 = append(msgs1, []*SigMsg{})
				}
				if vcMsg.State[i] == 0{
					rev0[i]++
					msgs0[i] = vcMsg.Msgs[i]
				}else{
					rev1[i]++
					msgs1[i] = append(msgs1[i], vcMsg.Msgs[i])
				}
			}
		}
		state := make([]int, len(rev0))
		msgs2 := make([]*SigMsg, len(rev0))
		mtx2.Lock()
		for i := 0;i < len(rev0);i++{
			if rev0[i] > 0{
				if rev0[i] == 2 * F + 1 && PROPOSALS[0][i].State < 2{
					PROPOSALS[0][i].State = 2
					PROPOSALS[0][i].Time2 = float64(time.Time.UnixNano(time.Now())) / 1000000
				}
				msgs2[i] = msgs0[i]
				state[i] = 0
			}else if len(PROPOSALS[1]) > i && PROPOSALS[1][i].State >= 1{
				msgs2[i] = PROPOSALS[1][i].TSigMsg1
				state[i] = 1
			}else{
				nilArr := []int{msg.View, i, 1}
				nilArrJson, _ := json.Marshal(nilArr)
				nilArrHash := hash([]byte(nilArrJson))
				sigs := make([][]byte, len(msgs1[i]))
				for j := 0;j < len(msgs1[i]);j++{
					nilMsg := NilMsg{}
					json.Unmarshal(msgs1[i][j].Data, &nilMsg)
					sigs[j] = nilMsg.Sig
				}
				tSig, err := tbls.Recover(suite, PUBKEY, nilArrHash, sigs, 2 * F + 1, 3 * F + 1)
				if err != nil {
					fmt.Println("Recover failed in ViewChange1Router!")
				}
				nilArr2 := []int{msg.View, i, 2}
				nilArr2Json, _ := json.Marshal(nilArr2)
				nilArr2Hash := hash([]byte(nilArr2Json))
				nilArr2Sig, _ := tbls.Sign(suite, MY_PRIKEY, nilArr2Hash)
				nilMsg2 := NilMsg{nilArr2, tSig, nilArr2Sig}
				nilMsg2Json, _ := json.Marshal(nilMsg2)
				fmt.Println("send NilMsg:", nilMsg2)
				msgs2[i] = &SigMsg{msg.View, NODE_NUM, "ViewChange2", []byte(nilMsg2Json), nil}
				state[i] = -1
			}
		}
		mtx2.Unlock()
		newVcMsg := ViewChangeMsg{msgs2, state, 2}
		newVcMsgJson, _ := json.Marshal(newVcMsg)
		newVcMsgHash := hash([]byte(newVcMsgJson))
		newVcMsgSig, _ := tbls.Sign(suite, MY_PRIKEY, newVcMsgHash)
		sigMsg := SigMsg{NODE_NUM, msg.View, "ViewChange2", []byte(newVcMsgJson), newVcMsgSig}
		sigMsgJson, _ := json.Marshal(sigMsg)
		bdMsg(7, []byte(sigMsgJson))
	}
	mtx3.Unlock()
}

type ViewChange2Router struct {
	znet.BaseRouter
}

func (r *ViewChange2Router) Handle(request ziface.IRequest){
	mtx4.RLock()
	view := VIEW
	mtx4.RUnlock()
	
	jsonStr := string(request.GetData())
	msg := SigMsg{}
	err := json.Unmarshal([]byte(jsonStr), &msg)
	if err != nil {
		fmt.Println("unmarshal failed in ViewChange2Router!")
		return
	}
	
	suite := bn256.NewSuite()
	hashValue := hash(msg.Data)
	err = bls.Verify(suite, PUBKEYS[msg.SenderId].V, hashValue, msg.Sig[2:])
	if err != nil{
		fmt.Println("签名验证失败1(ViewChange2Router)", err)
		return
	}
	
	vcMsg := ViewChangeMsg{}
	err = json.Unmarshal(msg.Data, &vcMsg)
	if err != nil {
		fmt.Println("unmarshal failed in ViewChange2Router!")
		return
	}
	
	if vcMsg.Phase != 2{
		fmt.Println("Phase错误(ViewChange2Router!)")
		return
	}
	
	if msg.View < view{
		fmt.Println("msg.View=", msg.View, "view=", view)
		return
	}
	
	if len(vcMsg.State) != len(vcMsg.Msgs){
		fmt.Println("长度错误(ViewChange2Router)")
		return
	}
	
	for i := 0;i < len(vcMsg.State);i++{
		if vcMsg.State[i] >= 0{
			err = bls.Verify(suite, PUBKEY.Commit(), PROPOSALS[vcMsg.State[i]][i].Hash[0:], vcMsg.Msgs[i].Sig)
			if err != nil{
				fmt.Println("签名验证失败2(ViewChange2Router)")
				return
			}
		}else if vcMsg.State[i] == -1{
			nilMsg := NilMsg{}
			err := json.Unmarshal([]byte(jsonStr), &nilMsg)
			if err != nil {
				fmt.Println("unmarshal failed in ViewChange2Router!")
				return
			}
			nilArr1 := []int{msg.View, i, 1}
			nilArr2 := nilMsg.Arr
			nilArr1Json, _ := json.Marshal(nilArr1)
			nilArr2Json, _ := json.Marshal(nilArr2)
			nilArr1Hash := hash([]byte(nilArr1Json))
			nilArr2Hash := hash([]byte(nilArr2Json))
			if len(nilArr2) < 3 || nilArr2[0] != msg.View || nilArr2[1] != i || nilArr2[2] != 2{
				fmt.Println("nilMsg错误(ViewChange2Router)")
				return
			}
			
			err = bls.Verify(suite, PUBKEY.Commit(), nilArr1Hash, nilMsg.Proof)
			if err != nil{
				fmt.Println("签名验证失败4(ViewChange2Router)")
				return
			}
			
			err = bls.Verify(suite, PUBKEYS[vcMsg.Msgs[i].SenderId].V, nilArr2Hash, nilMsg.Sig[2:])
			if err != nil{
				fmt.Println("签名验证失败3(ViewChange2Router)")
				return
			}
		}else{
			fmt.Println("state错误(ViewChange2Router)")
			return
		}
	}
	
	mtx5.Lock()
	_, ok := VIEWCHANGE2[msg.View]
	if !ok{
		VIEWCHANGE2[msg.View] = &ViewChangeCache{map[int]*SigMsg{}, false}
	}
	VIEWCHANGE2[msg.View].Msgs[msg.SenderId] = &msg
	
	if !VIEWCHANGE2[msg.View].End && len(VIEWCHANGE2[msg.View].Msgs) == 2 * F + 1{
		VIEWCHANGE2[msg.View].End = true
		if view < msg.View{
			mtx4.Lock()
			VIEW = msg.View
			mtx4.Unlock()
		}
		
		rev0 := []int{}
		rev1 := []int{}
		rev_1 := []int{}
		msgs0 := []*SigMsg{}
		msgs1 := []*SigMsg{}
		msgs_1 := [][]*SigMsg{}
		for _, v := range VIEWCHANGE2[msg.View].Msgs{
			vcMsg := ViewChangeMsg{}
			json.Unmarshal(v.Data, &vcMsg)
			for i := 0;i < len(vcMsg.State);i++{
				if len(rev0) <= i{
					rev0 = append(rev0, 0)
					rev1 = append(rev1, 0)
					rev_1 = append(rev_1, 0)
					msgs0 = append(msgs0, nil)
					msgs1 = append(msgs1, nil)
					msgs_1 = append(msgs_1, []*SigMsg{})
				}
				if vcMsg.State[i] == 0{
					rev0[i]++
					msgs0[i] = vcMsg.Msgs[i]
				}else if vcMsg.State[i] == 1{
					rev1[i]++
					msgs1[i] = vcMsg.Msgs[i]
				}else if vcMsg.State[i] == -1{
					rev_1[i]++
					msgs_1[i] = append(msgs_1[i], vcMsg.Msgs[i])
				}
			}
		}
		
		state := make([]int, len(rev0))
		msgs2 := make([]*SigMsg, len(rev0))
		mtx2.Lock()
		for i := 0;i < len(rev0);i++{
			if rev0[i] == 2 * F + 1{
				if PROPOSALS[0][i].State < 2{
					PROPOSALS[0][i].State = 2
					PROPOSALS[0][i].Time2 = float64(time.Time.UnixNano(time.Now())) / 1000000
				}
				msgs2[i] = msgs0[i]
				state[i] = 0
			}else if rev1[i] > 0{
				if rev1[i] == 2 * F + 1 && PROPOSALS[1][i].State < 3{
					PROPOSALS[1][i].State = 3
					PROPOSALS[1][i].Time2 = float64(time.Time.UnixNano(time.Now())) / 1000000
				}
				msgs2[i] = msgs1[i]
				state[i] = 1
			}else{
				nilArr2 := []int{msg.View, i, 2}
				nilArr2Json, _ := json.Marshal(nilArr2)
				nilArr2Hash := hash([]byte(nilArr2Json))
				sigs := make([][]byte, len(msgs_1[i]))
				for j := 0;j < len(msgs_1[i]);j++{
					nilMsg := NilMsg{}
					json.Unmarshal(msgs_1[i][j].Data, &nilMsg)
					sigs[j] = nilMsg.Sig
				}
				tSig, err := tbls.Recover(suite, PUBKEY, nilArr2Hash, sigs, 2 * F + 1, 3 * F + 1)
				if err != nil {
					fmt.Println("Recover failed in ViewChange2Router!")
				}
				
				nilArr3 := []int{msg.View, i, 3}
				nilArr3Json, _ := json.Marshal(nilArr3)
				nilArr3Hash := hash([]byte(nilArr3Json))
				nilArr3Sig, _ := tbls.Sign(suite, MY_PRIKEY, nilArr3Hash)
				nilMsg3 := NilMsg{nilArr3, tSig, nilArr3Sig}
				nilMsg3Json, _ := json.Marshal(nilMsg3)
				msgs2[i] = &SigMsg{msg.View, NODE_NUM, "ViewChange3", []byte(nilMsg3Json), nil}
				state[i] = -1
			}
		}
		mtx2.Unlock()
		
		newVcMsg := ViewChangeMsg{msgs2, state, 3}
		newVcMsgJson, _ := json.Marshal(newVcMsg)
		newVcMsgHash := hash([]byte(newVcMsgJson))
		newVcMsgSig, _ := tbls.Sign(suite, MY_PRIKEY, newVcMsgHash)
		sigMsg := SigMsg{NODE_NUM, msg.View, "ViewChange3", []byte(newVcMsgJson), newVcMsgSig}
		sigMsgJson, _ := json.Marshal(sigMsg)
		bdMsg(8, []byte(sigMsgJson))
	}
	mtx5.Unlock()
}

type ViewChange3Router struct {
	znet.BaseRouter
}

func (r *ViewChange3Router) Handle(request ziface.IRequest){
	mtx4.RLock()
	view := VIEW
	mtx4.RUnlock()
	
	jsonStr := string(request.GetData())
	msg := SigMsg{}
	err := json.Unmarshal([]byte(jsonStr), &msg)
	if err != nil {
		fmt.Println("unmarshal failed in ViewChange2Router!")
		return
	}
	
	suite := bn256.NewSuite()
	hashValue := hash(msg.Data)
	err = bls.Verify(suite, PUBKEYS[msg.SenderId].V, hashValue, msg.Sig[2:])
	if err != nil{
		fmt.Println("签名验证失败1(ViewChange3Router)", err)
		return
	}
	
	vcMsg := ViewChangeMsg{}
	err = json.Unmarshal(msg.Data, &vcMsg)
	if err != nil {
		fmt.Println("unmarshal failed in ViewChange3Router!")
		return
	}
	
	if vcMsg.Phase != 3{
		fmt.Println("Phase错误(ViewChange3Router!)")
		return
	}
	
	if msg.View < view{
		fmt.Println("msg.View=", msg.View, "view=", view)
		return
	}
	
	if len(vcMsg.State) != len(vcMsg.Msgs){
		fmt.Println("长度错误(ViewChange2Router)")
		return
	}
	
	for i := 0;i < len(vcMsg.State);i++{
		if vcMsg.State[i] >= 0{
			err = bls.Verify(suite, PUBKEY.Commit(), PROPOSALS[vcMsg.State[i]][i].Hash[0:], vcMsg.Msgs[i].Sig)
			if err != nil{
				fmt.Println("签名验证失败2(ViewChange3Router)")
				return
			}
		}else if vcMsg.State[i] == -1{
			nilMsg := NilMsg{}
			err := json.Unmarshal([]byte(jsonStr), &nilMsg)
			if err != nil {
				fmt.Println("unmarshal failed in ViewChange3Router!")
				return
			}
			nilArr2 := []int{msg.View, i, 2}
			nilArr3 := nilMsg.Arr
			nilArr2Json, _ := json.Marshal(nilArr2)
			nilArr3Json, _ := json.Marshal(nilArr3)
			nilArr2Hash := hash([]byte(nilArr2Json))
			nilArr3Hash := hash([]byte(nilArr3Json))
			if len(nilArr3) < 3 || nilArr3[0] != msg.View || nilArr3[1] != i || nilArr3[2] != 3{
				fmt.Println("nilMsg错误(ViewChange3Router)")
				return
			}
			
			err = bls.Verify(suite, PUBKEY.Commit(), nilArr2Hash, nilMsg.Proof)
			if err != nil{
				fmt.Println("签名验证失败4(ViewChange3Router)")
				return
			}
			
			err = bls.Verify(suite, PUBKEYS[vcMsg.Msgs[i].SenderId].V, nilArr3Hash, nilMsg.Sig[2:])
			if err != nil{
				fmt.Println("签名验证失败3(ViewChange3Router)")
				return
			}
		}else{
			fmt.Println("state错误(ViewChange3Router)")
			return
		}
	}
	
	mtx6.Lock()
	_, ok := VIEWCHANGE3[msg.View]
	if !ok{
		VIEWCHANGE3[msg.View] = &ViewChangeCache{map[int]*SigMsg{}, false}
	}
	VIEWCHANGE3[msg.View].Msgs[msg.SenderId] = &msg
	
	if !VIEWCHANGE3[msg.View].End && len(VIEWCHANGE3[msg.View].Msgs) == 2 * F + 1{
		VIEWCHANGE3[msg.View].End = true
		if view < msg.View{
			mtx4.Lock()
			VIEW = msg.View
			mtx4.Unlock()
		}
		
		rev0 := []int{}
		rev1 := []int{}
		rev_1 := []int{}
		for _, v := range VIEWCHANGE3[msg.View].Msgs{
			vcMsg := ViewChangeMsg{}
			json.Unmarshal(v.Data, &vcMsg)
			for i := 0;i < len(vcMsg.State);i++{
				if len(rev0) <= i{
					rev0 = append(rev0, 0)
					rev1 = append(rev1, 0)
					rev_1 = append(rev_1, 0)
				}
				if vcMsg.State[i] == 0{
					rev0[i]++
				}else if vcMsg.State[i] == 1{
					rev1[i]++
				}else if vcMsg.State[i] == -1{
					rev_1[i]++
				}
			}
		}
		
		for i := 0;i < len(rev0);i++{
			if rev0[i] == 2 * F + 1{
				if PROPOSALS[0][i].State < 2{
					PROPOSALS[0][i].State = 2
					PROPOSALS[0][i].Time2 = float64(time.Time.UnixNano(time.Now())) / 1000000
				}
			}else if rev1[i] == 2 * F + 1 && PROPOSALS[1][i].State < 3{
				PROPOSALS[1][i].State = 3
				PROPOSALS[1][i].Time2 = float64(time.Time.UnixNano(time.Now())) / 1000000
			}
		}
		if VCTIME_END == -1{
			VCTIME_END = float64(time.Time.UnixNano(time.Now())) / 1000000
		}
		go reStart()
	}
	
	mtx6.Unlock()
}

type PingRouter struct {
	znet.BaseRouter
}

func (r *PingRouter) Handle(request ziface.IRequest){
	fmt.Println("msg from node ", string(request.GetData()))
}

func SwitchHandler(w http.ResponseWriter, r *http.Request) {
    RUNNING = !RUNNING
	fmt.Fprintln(w, "hello world")
}

func LatencyHandler(w http.ResponseWriter, r *http.Request) {
	/*
    arr := [2][]float64{}
	for i := 0;i < len(PROPOSALS[0]);i++{
		if PROPOSALS[0][i].Time1 != -1 && PROPOSALS[0][i].Time2 != -1{
			arr[0] = append(arr[0], PROPOSALS[0][i].Time2 - PROPOSALS[0][i].Time1)
		}else{
			arr[0] = append(arr[0], -1)
		}
	}
	
	for i := 0;i < len(PROPOSALS[1]);i++{
		if PROPOSALS[1][i].Time1 != -1 && PROPOSALS[1][i].Time2 != -1{
			arr[1] = append(arr[1], PROPOSALS[1][i].Time2 - PROPOSALS[1][i].Time1)
		}else{
			arr[1] = append(arr[1], -1)
		}
	}
	if VCTIME_END != -1 && VCTIME_START != -1{
		fmt.Fprintln(w, arr, VCTIME_END - VCTIME_START)
	}else{
		fmt.Fprintln(w, arr)
	}
	*/
	fmt.Fprintln(w, len(RECORD))
	for i := 0;i < len(RECORD);i++{
		fmt.Fprintln(w, RECORD[i])
	}
}

func main() {
	if len(os.Args) != 3{
		fmt.Println("参数数量错误")
		return
	}
	num, err := strconv.Atoi(os.Args[1])
	if err != nil{
		fmt.Println("节点号码必须是数字")
		return
	}
	if num >= 3 * F + 1 || num < 0{
		fmt.Println("节点号码错误")
		return
	}
	NODE_NUM = num
	ADDRESS = os.Args[2]
	arr := strings.Split(ADDRESS, ":")
	ip := arr[0]
	port, err := strconv.Atoi(arr[1])
	if err != nil{
		fmt.Println("端口必须是数字")
		return
	}
	
	fmt.Println("节点号:", NODE_NUM, " 地址:", ADDRESS)
	cryptoInit()
	
	REPLICAS[REGISTER] = &Replica{}
	REPLICAS[REGISTER].Address = REGISTER_ADDRESS
	
	go mainLoop()
	
	go func(){
		http.HandleFunc("/switch", SwitchHandler)
		http.HandleFunc("/latency", LatencyHandler)
		http.ListenAndServe(ip + ":" + strconv.Itoa(port - 1000), nil)
	}()
	
	s := znet.NewServer2(ip, port)
	s.AddRouter(1, &RegisterRouter{})
	s.AddRouter(2, &BDNodesRouter{})
	s.AddRouter(3, &PrePrepareRouter{})
	s.AddRouter(4, &PrepareRouter{})
	s.AddRouter(5, &CommitRouter{})
	s.AddRouter(6, &ViewChange1Router{})
	s.AddRouter(7, &ViewChange2Router{})
	s.AddRouter(8, &ViewChange3Router{})
	s.AddRouter(10, &PingRouter{})
	
	if NODE_NUM != REGISTER{
		register()
	}
	
	s.Serve()
}