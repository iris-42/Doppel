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
	"sort"
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
var PROPOSALS = []*Proposal{}
var mtx1 sync.RWMutex //for REPLICAS
var mtx2 sync.RWMutex //for PROPOSALS
var PARELLEL_PROPOSALS = 0
var TIMER *time.Timer = nil
var TIMEOUT time.Duration = 2000
var MSGID = 0
var STOP = false
var VIEWCHANGEMSGS = make([]map[int]*SigMsg, 1)
var mtx3 sync.RWMutex //for VIEWCHANGEMSGS
var mtx4 sync.RWMutex //for VIEW
var VCTIME_START = -1.0
var VCTIME_END = -1.0
var LOAD = 0
var BDNODES = false
var RECOND = [][]float64{}

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
}

type VoteMsg struct{
	MsgId int
	Phase int
	Hash []byte
}

type SigMsg struct{
	SenderId int
	View int
	Type string
	Data []byte
	Sig []byte
}

type ViewChangeMsg struct{
	Length int
	Msgs []*SigMsg
}

type NewViewMsg struct{
	PrePrepareMsgs []*PrePrepareMsg
	Proofs []*ViewChangeMsg
}

func hash(data []byte) []byte{
	hash := sha256.New()
	hash.Write(data)
	return hash.Sum(nil)
}

func reStart(){
	time.Sleep(5 * time.Second)
	arr := []float64{}
	for i := 0;i < len(PROPOSALS);i++{
		if PROPOSALS[i].Time1 != -1 && PROPOSALS[i].Time2 != -1{
			arr = append(arr, PROPOSALS[i].Time2 - PROPOSALS[i].Time1)
		}else{
			arr = append(arr, -1)
		}
	}
	RECOND = append(RECOND, arr)
	
	if VCTIME_START != -1 && VCTIME_END != -1{
		RECOND = append(RECOND, []float64{VCTIME_END - VCTIME_START})
	}
	
	fmt.Println("reStart...")
	
	VIEW = 0
	PROPOSALS = []*Proposal{}
	PARELLEL_PROPOSALS = 0
	VIEWCHANGEMSGS = make([]map[int]*SigMsg, 1)
	VCTIME_START = -1.0
	VCTIME_END = -1.0
	STOP = false
	
	if NODE_NUM == getLeader(VIEW){
		time.Sleep(5 * time.Second)
		RUNNING = true
	}
	
}

func timeoutCheck(){
	for ;;{
		select{
			case <- TIMER.C:
				mtx4.Lock()
				VIEW++
				view := VIEW
				mtx4.Unlock()
				fmt.Println("超时,新Leader ", getLeader(view))
				VCTIME_START = float64(time.Time.UnixNano(time.Now())) / 1000000
				STOP = true
				RUNNING = false
				msgs := []*SigMsg{}
				mtx2.Lock()
				for i := 0;i < len(PROPOSALS);i++{
					if PROPOSALS[i].State >= 1{
						msgs = append(msgs, PROPOSALS[i].TSigMsg1)
					}
				}
				mtx2.Unlock()
				viewChangeMsg := ViewChangeMsg{len(msgs), msgs}
				viewChangeMsgJson, _ := json.Marshal(viewChangeMsg)
				viewChangeMsgHash := hash([]byte(viewChangeMsgJson))
				suite := bn256.NewSuite()
				sig, _ := tbls.Sign(suite, MY_PRIKEY, viewChangeMsgHash)
				sigMsg := SigMsg{NODE_NUM, view, "ViewChange", []byte(viewChangeMsgJson), sig}
				sigMsgJson, _ := json.Marshal(sigMsg)
				mtx3.Lock()
				if len(VIEWCHANGEMSGS) == view{
					VIEWCHANGEMSGS = append(VIEWCHANGEMSGS, map[int]*SigMsg{NODE_NUM: &sigMsg})
				}else{
					VIEWCHANGEMSGS[view][NODE_NUM] = &sigMsg
				}
				mtx3.Unlock()
				if NODE_NUM != getLeader(view){
					sendMsg(getLeader(view), 6, []byte(sigMsgJson))
				}
		}
	}
}

func getLeader(num int) int{
	return (num) % (3 * F + 1)
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
		if RUNNING && NODE_NUM == getLeader(view) && PARELLEL_PROPOSALS < 1{
			Id := len(PROPOSALS)
			newPrePrepareMsg := PrePrepareMsg{Id, []byte(data)}
			newPrePrepareJson, _ := json.Marshal(newPrePrepareMsg)
			newPrePrepareHash := hash([]byte(newPrePrepareJson))
			suite := bn256.NewSuite()
			newPrePrepareSig, _ := tbls.Sign(suite, MY_PRIKEY, newPrePrepareHash)
			sigMsg := SigMsg{NODE_NUM, view, "PrePrepare", []byte(newPrePrepareJson), newPrePrepareSig}
			sigMsgJson, _ := json.Marshal(sigMsg)
			sigMsgByte := []byte(sigMsgJson)
			
			voteMsg1 := VoteMsg{Id, 1, newPrePrepareHash}
			voteJson1, _ := json.Marshal(voteMsg1)
			voteHash1 := hash([]byte(voteJson1))
			voteSig1, _ := tbls.Sign(suite, MY_PRIKEY, voteHash1)
			prepareMsg := SigMsg{NODE_NUM, view, "Prepare", []byte(voteJson1), voteSig1}
			
			voteMsg2 := VoteMsg{Id, 2, newPrePrepareHash}
			voteJson2, _ := json.Marshal(voteMsg2)
			voteHash2 := hash([]byte(voteJson2))
			voteSig2, _ := tbls.Sign(suite, MY_PRIKEY, voteHash2)
			commitMsg := SigMsg{NODE_NUM, view, "Commit", []byte(voteJson2), voteSig2}
			
			tempArr := [32]byte{}
			copy(tempArr[:], newPrePrepareHash)
			mtx2.Lock()
			nowTime := float64(time.Time.UnixNano(time.Now())) / 1000000
			PROPOSALS = append(PROPOSALS, &Proposal{&newPrePrepareMsg, tempArr, 0, map[int]*SigMsg{NODE_NUM: &prepareMsg}, map[int]*SigMsg{NODE_NUM: &commitMsg}, nil, nil, nowTime, -1})
			PARELLEL_PROPOSALS++
			
			arr := []int{}
			for i := 0;i < len(PROPOSALS);i++{
				arr = append(arr, PROPOSALS[i].State)
			}
			fmt.Println(arr)
			
			mtx2.Unlock()
			
			bdMsg(3, sigMsgByte)
			
			Id++
			fmt.Println("发送PrePrepare消息：", newPrePrepareHash)
		}else if NODE_NUM != getLeader(view){
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
	time.Sleep(time.Second * 3)
	mtx1.Unlock()
	if !BDNODES{
		bdMsg(10, []byte(strconv.Itoa(NODE_NUM)))
		BDNODES = true
	}
}

type PrePrepareRouter struct {
	znet.BaseRouter
}

func (r *PrePrepareRouter) Handle(request ziface.IRequest){
	fmt.Println("开始处理PrePrepare消息")
	
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
	
	if msg.View != view{
		fmt.Println("View错误(PrePrepareRouter)")
		return
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
	
	if msg.SenderId != getLeader(view){
		fmt.Println("消息发送者的身份错误(PrePrepareRouter)")
		return
	}
	
	newPrePrepareMsg := PrePrepareMsg{}
	err = json.Unmarshal([]byte(msg.Data), &newPrePrepareMsg)
	if err != nil {
		fmt.Println("unmarshal failed in PrePrepareRouter()!")
		return
	}
	
	mtx2.Lock()
	for newPrePrepareMsg.MsgId >= len(PROPOSALS){
		PROPOSALS = append(PROPOSALS, &Proposal{nil, [32]byte{}, -1, map[int]*SigMsg{}, map[int]*SigMsg{}, nil, nil, -1, -1})
	}
		
	if PROPOSALS[newPrePrepareMsg.MsgId].State != -1{
		mtx2.Unlock()
		return
	}else{
		PROPOSALS[newPrePrepareMsg.MsgId].Msg = &newPrePrepareMsg
		PROPOSALS[newPrePrepareMsg.MsgId].State = 0
		tempArr := [32]byte{}
		copy(tempArr[:], hashValue)
		PROPOSALS[newPrePrepareMsg.MsgId].Hash = tempArr
	}
	mtx2.Unlock()
		
	voteMsg := VoteMsg{newPrePrepareMsg.MsgId, 1, hashValue}
	voteJson, _ := json.Marshal(voteMsg)
	voteHash := hash([]byte(voteJson))
	voteSig, _ := tbls.Sign(suite, MY_PRIKEY, voteHash)
	prepareMsg := SigMsg{NODE_NUM, view, "Prepare", []byte(voteJson), voteSig}
	prepareMsgJson, _ := json.Marshal(prepareMsg)
	
	sendMsg(getLeader(view), 4, []byte(prepareMsgJson))
	
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
	
	fmt.Println("PrePrepare消息处理结束")
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
	
	prepareMsg := VoteMsg{}
	err = json.Unmarshal(msg.Data, &prepareMsg)
	if err != nil {
		fmt.Println("unmarshal failed in PrepareRouter!")
		return
	}
	
	fmt.Println("开始处理来自node", msg.SenderId ,"的Prepare消息with MsgId", prepareMsg.MsgId, " and Phase", prepareMsg.Phase)
	
	/********************ONLY FOR TEST!!!!!!!!!!********************/
	if prepareMsg.MsgId == 5 && NODE_NUM == 0 && prepareMsg.Phase == 2{
		if VCTIME_START == -1{
			VCTIME_START = float64(time.Time.UnixNano(time.Now())) / 1000000
		}
		return
	}
	/********************ONLY FOR TEST!!!!!!!!!!********************/
	
	mtx2.Lock()
	if prepareMsg.MsgId >= len(PROPOSALS){
		fmt.Println("无效的Prepare消息(PrepareRouter)")
		mtx2.Unlock()
		return
	}
	tempArr := [32]byte{}
	copy(tempArr[:], prepareMsg.Hash)
	if tempArr != PROPOSALS[prepareMsg.MsgId].Hash{
		fmt.Println("无效的Prepare消息(PrepareRouter)")
		mtx2.Unlock()
		return
	}
	if prepareMsg.Phase == 1{
		if PROPOSALS[prepareMsg.MsgId].State < 1{
			PROPOSALS[prepareMsg.MsgId].PrepareMsgs[msg.SenderId] = &msg
			if len(PROPOSALS[prepareMsg.MsgId].PrepareMsgs) >= 2 * F + 1{
				sigs := make([][]byte, len(PROPOSALS[prepareMsg.MsgId].PrepareMsgs))
				i := 0
				for _, msg := range PROPOSALS[prepareMsg.MsgId].PrepareMsgs{
					sigs[i] = msg.Sig
					i++
				}
				tSig, _ := tbls.Recover(suite, PUBKEY, hashValue, sigs, 2 * F + 1, 3 * F + 1)
				commitMsg := SigMsg{NODE_NUM, view, "Commit", msg.Data, tSig}
				PROPOSALS[prepareMsg.MsgId].TSigMsg1 = &commitMsg
				CommitMsgJson, _ := json.Marshal(commitMsg)
				PROPOSALS[prepareMsg.MsgId].State = 1
				/********************ONLY FOR TEST!!!!!!!!!!********************/
				/*
				if prepareMsg.MsgId == 5 && NODE_NUM == 0{
					for i := 1;i <= F;i++{
						go sendMsg(i, 5, []byte(CommitMsgJson))
					}
					if VCTIME_START == -1{
						VCTIME_START = float64(time.Time.UnixNano(time.Now())) / 1000000
					}
				}else{
					bdMsg(5, []byte(CommitMsgJson))
				}
				*/
				/********************ONLY FOR TEST!!!!!!!!!!********************/
				bdMsg(5, []byte(CommitMsgJson))
			}
		}else if view != PROPOSALS[prepareMsg.MsgId].TSigMsg1.View{
			commitMsg := SigMsg{NODE_NUM, view, "Commit", PROPOSALS[prepareMsg.MsgId].TSigMsg1.Data, PROPOSALS[prepareMsg.MsgId].TSigMsg1.Sig}
			commitMsgJson, _ := json.Marshal(commitMsg)
			sendMsg(msg.SenderId, 5, []byte(commitMsgJson))
		}
	}else if prepareMsg.Phase == 2{
		if PROPOSALS[prepareMsg.MsgId].State < 2{
			PROPOSALS[prepareMsg.MsgId].PreCommitMsgs[msg.SenderId] = &msg
			if len(PROPOSALS[prepareMsg.MsgId].PreCommitMsgs) >= 2 * F + 1{
				sigs := make([][]byte, len(PROPOSALS[prepareMsg.MsgId].PreCommitMsgs))
				i := 0
				for _, msg := range PROPOSALS[prepareMsg.MsgId].PreCommitMsgs{
					sigs[i] = msg.Sig
					i++
				}
				tSig, _ := tbls.Recover(suite, PUBKEY, hashValue, sigs, 2 * F + 1, 3 * F + 1)
				commitMsg := SigMsg{NODE_NUM, view, "Commit", msg.Data, tSig}
				PROPOSALS[prepareMsg.MsgId].TSigMsg2 = &commitMsg
				CommitMsgJson, _ := json.Marshal(commitMsg)
				bdMsg(5, []byte(CommitMsgJson))
				PROPOSALS[prepareMsg.MsgId].State = 2
				PROPOSALS[prepareMsg.MsgId].Time2 = float64(time.Time.UnixNano(time.Now())) / 1000000
				PARELLEL_PROPOSALS--
			}
		}else if view != PROPOSALS[prepareMsg.MsgId].TSigMsg2.View{
			commitMsg := SigMsg{NODE_NUM, view, "Commit", PROPOSALS[prepareMsg.MsgId].TSigMsg2.Data, PROPOSALS[prepareMsg.MsgId].TSigMsg2.Sig}
			commitMsgJson, _ := json.Marshal(commitMsg)
			sendMsg(msg.SenderId, 5, []byte(commitMsgJson))
		}
	}else{
		fmt.Println("错误的Phase(PrepareRouter)")
		mtx2.Unlock()
		return
	}
	mtx2.Unlock()
	
	fmt.Println("Prepare消息处理结束")
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
	
	if msg.View != view{
		fmt.Println("View错误(CommitRouter)", msg.View, view)
		return
	}
	
	if msg.Type != "Commit"{
		fmt.Println("错误的消息类型(CommitRouter)")
		return
	}
	
	commitMsg := VoteMsg{}
	err = json.Unmarshal(msg.Data, &commitMsg)
	if err != nil {
		fmt.Println("unmarshal failed in CommitRouter!")
		return
	}
	
	fmt.Println("开始处理来自node", msg.SenderId ,"的PreCommit消息with MsgId", commitMsg.MsgId, " and Phase", commitMsg.Phase)
	
	suite := bn256.NewSuite()
	hashValue := hash(msg.Data)
	err = bls.Verify(suite, PUBKEY.Commit(), hashValue, msg.Sig)
	if err != nil{
		fmt.Println("签名验证失败(CommitRouter)")
		return
	}
	
	if msg.SenderId != getLeader(view){
		fmt.Println("消息发送者的身份错误(CommitRouter)")
		return
	}
	
	mtx2.Lock()
	for commitMsg.MsgId >= len(PROPOSALS){
		PROPOSALS = append(PROPOSALS, &Proposal{nil, [32]byte{}, -1, map[int]*SigMsg{}, map[int]*SigMsg{}, nil, nil, -1, -1})
	}
	if commitMsg.Phase == 1{
		if PROPOSALS[commitMsg.MsgId].State < commitMsg.Phase{
			PROPOSALS[commitMsg.MsgId].State = 1
			PROPOSALS[commitMsg.MsgId].TSigMsg1 = &msg
		}
		voteMsg := VoteMsg{commitMsg.MsgId, 2, commitMsg.Hash}
		voteJson, _ := json.Marshal(voteMsg)
		voteHash := hash([]byte(voteJson))
		voteSig, _ := tbls.Sign(suite, MY_PRIKEY, voteHash)
		prepareMsg := SigMsg{NODE_NUM, view, "Prepare", []byte(voteJson), voteSig}
		prepareMsgJson, _ := json.Marshal(prepareMsg)
		sendMsg(getLeader(view), 4, []byte(prepareMsgJson))
	}else{
		if PROPOSALS[commitMsg.MsgId].State < commitMsg.Phase{
			PROPOSALS[commitMsg.MsgId].State = 2
			PROPOSALS[commitMsg.MsgId].TSigMsg2 = &msg
			PROPOSALS[commitMsg.MsgId].Time2 = float64(time.Time.UnixNano(time.Now())) / 1000000
		}
	}
	arr := []int{}
	for i := 0;i < len(PROPOSALS);i++{
		arr = append(arr, PROPOSALS[i].State)
	}
	fmt.Println(arr)
	mtx2.Unlock()
	
	fmt.Println("PrepareCommit消息处理结束2")
}

type ViewChangeRouter struct {
	znet.BaseRouter
}

func (r *ViewChangeRouter) Handle(request ziface.IRequest){
	mtx4.RLock()
	view := VIEW
	mtx4.RUnlock()
	
	jsonStr := string(request.GetData())
	msg := SigMsg{}
	err := json.Unmarshal([]byte(jsonStr), &msg)
	if err != nil {
		fmt.Println("unmarshal failed in ViewChangeRouter!")
		return
	}
	
	fmt.Println("开始处理ViewChange消息来自node ", msg.SenderId)
	
	if msg.View < view{
		fmt.Println("view错误(ViewChangeRouter)")
		return
	}
	
	if getLeader(msg.View) != NODE_NUM{
		fmt.Println("错误的备用Leader(ViewChangeRouter)")
		return
	}
	
	if msg.Type != "ViewChange"{
		fmt.Println("错误的消息类型(ViewChangeRouter)")
		return
	}
	
	suite := bn256.NewSuite()
	hashValue := hash(msg.Data)
	err = bls.Verify(suite, PUBKEYS[msg.SenderId].V, hashValue, msg.Sig[2:])
	if err != nil{
		fmt.Println("签名验证失败(ViewChangeRouter)")
		return
	}
	
	viewChangeMsg := ViewChangeMsg{}
	err = json.Unmarshal(msg.Data, &viewChangeMsg)
	if err != nil {
		fmt.Println("unmarshal failed in ViewChangeRouter!")
		return
	}
	
	for i := 0;i < viewChangeMsg.Length;i++{
		err = bls.Verify(suite, PUBKEY.Commit(), hash(viewChangeMsg.Msgs[i].Data), viewChangeMsg.Msgs[i].Sig)
		if err != nil{
			fmt.Println("签名验证失败(ViewChangeRouter)")
			return
		}
	}
	
	mtx3.Lock()
	for ;len(VIEWCHANGEMSGS) <= msg.View;{
		VIEWCHANGEMSGS = append(VIEWCHANGEMSGS, map[int]*SigMsg{})
	}
	VIEWCHANGEMSGS[msg.View][msg.SenderId] = &msg
	proofs := []*ViewChangeMsg{}
	if len(VIEWCHANGEMSGS[msg.View]) >= 2 * F + 1{
		mtx4.Lock()
		VIEW = msg.View
		mtx4.Unlock()
		proofs = make([]*ViewChangeMsg, len(VIEWCHANGEMSGS[msg.View]))
		i := 0
		for _, v := range VIEWCHANGEMSGS[msg.View]{
			viewChangeMsg := ViewChangeMsg{}
			json.Unmarshal(v.Data, &viewChangeMsg)
			proofs[i] = &viewChangeMsg
			i++
		}
	}
	mtx3.Unlock()
	
	if len(proofs) == 2 * F + 1{
		STOP = false
		prePrepares := map[int]*PrePrepareMsg{}
		for i := 0;i < len(proofs);i++{
			for j := 0;j < proofs[i].Length;j++{
				voteMsg := VoteMsg{}
				err := json.Unmarshal(proofs[i].Msgs[j].Data, &voteMsg)
				if err != nil{
					fmt.Println("VoteMsg unmarshal failed")
				}
				prePrepares[voteMsg.MsgId] = &PrePrepareMsg{voteMsg.MsgId, voteMsg.Hash}
			}
		}
		prePrepareMsgs := []*PrePrepareMsg{}
		for _, v := range prePrepares{
			prePrepareMsgs = append(prePrepareMsgs, v)
			voteMsg1 := VoteMsg{v.MsgId, 1, v.Data}
			voteJson1, _ := json.Marshal(voteMsg1)
			voteHash1 := hash([]byte(voteJson1))
			voteSig1, _ := tbls.Sign(suite, MY_PRIKEY, voteHash1)
			prepareMsg := SigMsg{NODE_NUM, view, "Prepare", []byte(voteJson1), voteSig1}
				
			voteMsg2 := VoteMsg{v.MsgId, 2, v.Data}
			voteJson2, _ := json.Marshal(voteMsg2)
			voteHash2 := hash([]byte(voteJson2))
			voteSig2, _ := tbls.Sign(suite, MY_PRIKEY, voteHash2)
			commitMsg := SigMsg{NODE_NUM, view, "Commit", []byte(voteJson2), voteSig2}
			
			mtx2.Lock()
			PROPOSALS[v.MsgId].PrepareMsgs = map[int]*SigMsg{NODE_NUM: &prepareMsg}
			PROPOSALS[v.MsgId].PreCommitMsgs = map[int]*SigMsg{NODE_NUM: &commitMsg}
			mtx2.Unlock()
		}
		sort.Slice(prePrepareMsgs, func(i, j int) bool {
		  return prePrepareMsgs[i].MsgId <= prePrepareMsgs[j].MsgId
	   })
	   newViewMsg := NewViewMsg{prePrepareMsgs, proofs}
	   newViewMsgJson, _ := json.Marshal(newViewMsg)
	   newViewMsgHash := hash([]byte(newViewMsgJson))
	   newViewMsgSig, _ := tbls.Sign(suite, MY_PRIKEY, newViewMsgHash)
	   sigMsg := SigMsg{NODE_NUM, msg.View, "NewView", []byte(newViewMsgJson), newViewMsgSig}
	   sigMsgJson, _ := json.Marshal(sigMsg)
	   bdMsg(7, []byte(sigMsgJson))
	   RUNNING = true
	   PARELLEL_PROPOSALS = len(newViewMsg.PrePrepareMsgs)
	   go reStart()
	}
	
	fmt.Println("ViewChange消息处理结束")
}

type NewViewRouter struct {
	znet.BaseRouter
}

func (r *NewViewRouter) Handle(request ziface.IRequest){
	mtx4.Lock()
	view := VIEW
	mtx4.Unlock()
	
	fmt.Println("开始处理NewView消息")
	
	jsonStr := string(request.GetData())
	msg := SigMsg{}
	err := json.Unmarshal([]byte(jsonStr), &msg)
	if err != nil {
		fmt.Println("unmarshal failed in NewViewRouter!")
		return
	}
	
	if msg.View < view{
		return
	}
	
	suite := bn256.NewSuite()
	hashValue := hash(msg.Data)
	err = bls.Verify(suite, PUBKEYS[msg.SenderId].V, hashValue, msg.Sig[2:])
	if err != nil{
		fmt.Println("签名验证失败(NewViewRouter)")
		return
	}
	
	newViewMsg := NewViewMsg{}
	err = json.Unmarshal(msg.Data, &newViewMsg)
	if err != nil {
		fmt.Println("unmarshal failed in NewViewRouter!")
		return
	}
	
	for i := 0;i < len(newViewMsg.Proofs);i++{
		sigMsg := SigMsg{}
		err = json.Unmarshal([]byte(jsonStr), &sigMsg)
		if err != nil {
			fmt.Println("unmarshal failed in NewViewRouter!")
			return
		}
		hashValue := hash(sigMsg.Data)
		err = bls.Verify(suite, PUBKEYS[sigMsg.SenderId].V, hashValue, sigMsg.Sig[2:])
		if err != nil{
			fmt.Println("签名验证失败(NewViewRouter)")
			return
		}
	}
	
	mtx4.Lock()
	VIEW = msg.View
	mtx4.Unlock()
	STOP = false
	for ;len(VIEWCHANGEMSGS) <= msg.View;{
		VIEWCHANGEMSGS = append(VIEWCHANGEMSGS, map[int]*SigMsg{})
	}
	
	for i := 0;i < len(newViewMsg.PrePrepareMsgs);i++{
		voteMsg := VoteMsg{newViewMsg.PrePrepareMsgs[i].MsgId, 1, newViewMsg.PrePrepareMsgs[i].Data}
		voteMsgJson, _ := json.Marshal(voteMsg)
		voteMsgHash := hash([]byte(voteMsgJson))
		voteMsgSig, _ := tbls.Sign(suite, MY_PRIKEY, voteMsgHash)
		sigMsg := SigMsg{NODE_NUM, msg.View, "Prepare", []byte(voteMsgJson), voteMsgSig}
		sigMsgJson, _ := json.Marshal(sigMsg)
		sendMsg(getLeader(msg.View), 4, []byte(sigMsgJson))
	}
	
	if VCTIME_END == -1{
		VCTIME_END = float64(time.Time.UnixNano(time.Now())) / 1000000
	}
	fmt.Println("NewView消息处理结束")
	
	go reStart()
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
    arr := []float64{}
	for i := 0;i < len(PROPOSALS);i++{
		if PROPOSALS[i].Time1 != -1 && PROPOSALS[i].Time2 != -1{
			arr = append(arr, PROPOSALS[i].Time2 - PROPOSALS[i].Time1)
		}else{
			arr = append(arr, -1)
		}
	}
	if VCTIME_END != -1 && VCTIME_START != -1{
		fmt.Fprintln(w, arr, VCTIME_END - VCTIME_START)
	}else{
		fmt.Fprintln(w, arr, VCTIME_START, VCTIME_END)
	}*/
	fmt.Fprintln(w, len(RECOND))
	for i := 0;i < len(RECOND);i++{
		fmt.Fprintln(w, RECOND[i])
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
	s.AddRouter(6, &ViewChangeRouter{})
	s.AddRouter(7, &NewViewRouter{})
	s.AddRouter(10, &PingRouter{})
	
	if NODE_NUM != REGISTER{
		register()
	}
	
	s.Serve()
}
