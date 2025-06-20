module World
open RelCalc as r

-- inicio de assinaturas

sig Thread {
	fst: one Event,
}

sig Event {
	t: one Thread,
	So: lone Event,
	hb: set Event,
}

abstract sig Communication extends Event {}

sig Send extends Communication {}

sig Rcv extends Communication {
	sender: one Send
}

check {
	Function[sender,Rcv,Send]
} for 4

-- fim de assinaturas

-- utilidades
pred isFst [e:Event]{
	some e.~fst
}

fun sot[thr:Thread] : Event->Event {
	t.thr <: So
}
-- factos

-- o primeiro evento de uma thread é evento dessa thread
pred fstInThreadP { fst in ~t}

-- eventos relacionados por So estão na mesma thread
pred soInThread { So in ker[t] }

-- a So b_1 and ... b_m So b_m+1 ... and b_n So c then not c So a	
pred soAciclico {
	Acyclic[So, Event]
}

-- o primeiro evento de uma thread não tem predecessor
pred noPrevFst{
	no fst.So
}

-- um evento não pode ter mais que um sucessor
pred oneSuc {
	Injective[So,Event]
}

-- para todas as threads, o feixo transitivo de sua session order é uma ordem linear estrita
pred allSotTotal {
	all thr : Thread | Linearorder[^(sot[thr] + thr.fst->thr.fst) + id[t.thr], t.thr]
}

pred hbDef {
	hb = tc[Event,So + sender]
}

pred fstIsNotRecv {
	no fst.Rcv
}

pred correctBroadCast {
	no (ker[sender] - iden) & (ker[t] - iden)
}

fact {
	fstInThreadP
	soInThread
	oneSuc
	allSotTotal 
	hbDef
	noPrevFst
	correctBroadCast	
	Acyclic[So + sender,Event]
	fstIsNotRecv
}

-- fim de factos

-- verificacoes de redundancia & sanity checks

check redudancy { } for 6

check no_bcast_so_same_thread {
  all disj r1,r2 : Rcv | some r1.sender & r2.sender implies r1.t != r2.t
}

--- inicio de checks

check incomparable_roots {
	no hb & (Thread.fst -> Thread.fst)
} for 6

check rcvIsNotFst {
	all e:Rcv | not isFst[e]
}

check sanityCheckFstIsNotRcv{ all e:Event| no e.So implies e not in (Rcv)} for 6

check recvIsFuture {
	sender & ker[t] in  ^So
}

check initSend_ShouldFail {
  img[sender] in img[fst]
} for 6

check recvIsLast_ShouldFail  {
	all e:Event | ((some e.sender and  e.sender.t != e.t ) implies no So.e or some e.sender.~fst)
} for 6

check reachability {
	all thr : Thread |
		t.thr <: iden & Event->Event 
			in (*(sot[thr]) + *(~(sot[thr])))
}

--- fim de checks

run {
	some sender - ker[t] and
	some e:Send | some disj r1,r2,r3:Rcv | r1 in sender.e  and r2 in sender.e  and r3 in sender.e
} for exactly 7 Event, exactly 3 Thread
