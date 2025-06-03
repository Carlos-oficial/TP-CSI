open RelCalc as r


sig Thread {
	fst: one Event
}

sig Event {
	t: one Thread,
	So: lone Event,
	hb: set Event,
	sender: lone Event
	// sot_:set Event
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
	// Irreflexive[So]	
	// Antisymmetric[So,Event]
	// no cycles in So
	Acyclic[So,Event]
	
	// either first or there's a previous
	no fst.So
	// Entire[img[fst]+So,Event]
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

fact allSotTotal {
	all thr : Thread | Linearorder[^(sot[thr] + thr.fst->thr.fst) + id[t.thr], t.thr]
}

fact correctCommunications {
	Injective[sender,Event]
	Simple[sender,Event]
	Irreflexive[sender]
	Acyclic[So+sender,Event]
	no ker[sender] & img[sender]
}

fact {
	hb = tc[Event,So + sender]
}

check preorderHb{
	Preorder[hb+id[Event],Event]
}

check antiSym{
	Antisymmetric[hb+id[Event],Event]
}

check partorderHb{
	Partialorder[hb+id[Event],Event]
}

// --
run {all thr:Thread | some t.thr } for exactly 6 Event, exactly 3 Thread

run {some fst.So}
