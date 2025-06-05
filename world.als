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

fact {
	Bijection[sender,Rcv,Send]
}

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
	no ~fst.(Rcv + Send)
}

fact {
	fstInThreadP
	soInThread
	oneSuc
	allSotTotal 
	hbDef 
	noPrevFst
	-- soAciclico -- redundante
	Acyclic[So + sender,Event]
	fstIsNotRecv
}

-- fim de factos

-- verificacoes de redundancia
check redudancy { } for 6


--- inicio de checks

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

run {} for 8
