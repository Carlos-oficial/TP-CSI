open RelCalc as r

sig VClock {
	points : Thread -> one Int,
	prev: set VClock

}

fact {
  Bijection [clock, Event, VClock]
  all v : VClock | Entire[ v.points , Thread ]
}

fun init [] : VClock {
  { r: VClock | all n:Thread | r.points[n] = 0}
}

fun join[c1 : VClock, c2 : VClock]: VClock {
  { r: VClock |
    all n: Thread  |
      r.points[n] = (c1.points[n] >= c2.points[n] => c1.points[n] else c2.points[n])
  }
}

fun inc[n:Thread , c : VClock]: Thread ->Int {
 { n_ : Thread , i : Int | i = (n_ = n =>  add[ c.points[n_], 1] else c.points[n_])  }
}

pred gte[c1 : VClock, c2 : VClock] 
{
	all t : Thread | c1.points[t] >=  c2.points[t]
}

fact 
{
	all c1,c2 : VClock | c1 = prev[c2] iff (clock.c1).t = (clock.c2).t and c2.points[(clock.c2).t] = add[1,c1.points[(clock.c1).t]]
	all c:VClock | some fst.clock.c implies c = init[] -- pode-se verificar o iff
}


fact {
	So = clock . prev . ~clock
}

sig Thread {
	fst: one Event,
}

sig Event {
	t: one Thread,
	So: lone Event,
	hb: set Event,
	sender: lone Event,
	clock : one VClock
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

// -3
run {(all thr:Thread | some t.thr)} for exactly 3 Event, exactly 1 Thread, exactly 3 VClock

run {some fst.So}
