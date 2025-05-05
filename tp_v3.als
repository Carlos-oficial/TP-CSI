open RelCalc as r


sig Thread {
	fst: one Event
}

sig Event {
	t: one Thread,
	So: lone Event,
	hb: set Event,
	sender: lone Event
}

// fst 

fact fstInThread {
	fst in ~t
}

// So 

fact {
	// order in thread
	So in ker[t]
	
	//
	Irreflexive[So]	
	Antisymmetric[So,Event]
	// no cycles in So
	Acyclic[So,Event]

	// either first or there's a previous
	Entire[img[fst]++So,Event]
	Injective[So,Event]
}

check reachability {
	all thr : Thread |
		t.thr <: iden & Event->Event 
			in (*(sot[thr]) + *(~(sot[thr])))
}

fun sot[thr:Thread] : Event->Event {
	t.thr <: So
}

fact total {
	all t :Thread | Preorder[*(sot[t]),Event]
}




// communication

// abstract sig Communication extends Event {}

// sig Send extends Communication {}

//sig Rcv extends Communication {
//	sender: one Send
//}



fact correctCommunications {
	// sender ir not receiver
	// sender.t in t.(Thread->Thread-iden)
	Injective[sender,Event]
	Simple[sender,Event]
	Irreflexive[sender]
	// all sends have a sender
	// Send in Rcv.sender
}
// sanity checks
// check allSentRcvd { all s:Send | one sender.s }
// check allRcvdSent { all r:Rcv| one r.sender }
// happens before

fact {
	hb = ^(So + sender)
	// *So in hb
}

check preorderHb{
	Preorder[hb,Event]
}

// --
run {all thr:Thread | some t.thr } for exactly 6 Event, exactly 2 Thread
