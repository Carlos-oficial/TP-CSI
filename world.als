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

pred isFst [e:Event]{
	some e.~fst
}

pred initial [r:VClock]{
  all n:Thread | r.points[n] = 0
}

fun join[c1 : VClock, c2 : VClock]: VClock {
  { r: VClock |
    all n: Thread  |
      r.points[n] = (c1.points[n] >= c2.points[n] => c1.points[n] else c2.points[n])
  }
}

fun maxInt[i1: Int, i2 : Int]: Int {
  i1 >= i2 => i1 else i2
}

pred isJoin[ c1, c2, r: VClock] {
  all thr: Thread |
    r.points[thr] =
      (thr = (clock.r).t =>
        (maxInt[c1.points[thr], c2.points[thr]]).add[1]
      else 
        maxInt[c1.points[thr], c2.points[thr]])
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
	all c1,c2 : VClock | c1 = prev[c2] iff (clock.c1).t = (clock.c2).t 
	and c2.points[(clock.c2).t] = add[1,c1.points[(clock.c1).t]] 
	and (all thr : Thread -(clock.c2).t| c1.points[thr] = c2.points[thr])
	no fst.sender
	-- all c:VClock | one fst.clock.c implies c = init[] -- pode-se verificar o iff
	all thr:Thread | initial[thr.fst.clock]  -- pode-se verificar o iff
	
}

fact {
	So = clock . prev . ~clock
	all e:Event | some e.sender implies isJoin[e.sender.clock, e.So.clock, e.clock]
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

check initSend {
 all e:Event | (some e.sender and  e.sender.t != e.t ) implies some e.sender.~fst
}
// -3
run {(some e:Event | e.sender.t != e.t and some e.sender.t) and some sender }  for exactly 6 Event,exactly 6 VClock, exactly 2 Thread

run {some t1,t2:Thread | t1!=t2}
