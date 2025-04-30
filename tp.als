open RelCalc as r

sig Event {
	t: one Thread,
	So: lone Event,
	hb: set Event,
	fst: lone Event
}


abstract sig Communication extends Event {}

sig Send extends Communication {}

sig Rcv extends Communication {
	sender: one Send
}

sig Thread {
}

fact {
	fst in iden
	// thus ker[fst] = fst
	~fst.ker[t].fst in ker[t]

	fst.So in bottom
	ker[fst.t] in fst
	
	dom[So ++ fst] = Event
	
	// no So & iden
	//no ^~So & iden
	
	Acyclic[So,Event]
	Irreflexive[So]
	Injective[So,Event]
	So in ker[t]

	sender.t in t.(Thread->Thread-iden)
	Injective[sender,Rcv]
	Send in Rcv.sender
	
}

check noOneBeforeFst{
	no fst.So
}

check uniqueFst {
	all thr:Thread | some t.thr implies one fst.t.thr
}

fact {hb = ker[t]}

check preorderSo{
	all thr:Thread | Preorder[*(So)++fst,t.thr]
}
check partialorderSo{
	all thr:Thread | Partialorder[*(So)++fst,t.thr]
}

check linorderSo{
	all thr:Thread | Linearorder[*(So)++fst,t.thr]
}

run {all thr:Thread | some t.thr} for exactly 6 Event, exactly 2 Thread
