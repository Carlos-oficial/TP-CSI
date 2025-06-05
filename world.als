open RelCalc as r

-- inicio de assinaturas

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

sig VClock {
	event : one Event,
	points : Thread -> one Int,
	-- int points : Thread,
	prev: set VClock
}
-- fim de assinaturas


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

pred isPrev[c1 : VClock, c2 : VClock] 
{
	add[1,c1.points[(clock.c1).t]]  = c2.points[(clock.c1).t]
}

fun sot[thr:Thread] : Event->Event {
	t.thr <: So
}

-- inicio de factos

-- Eventos abstratos

-- o primeiro evento de uma thread é evento dessa thread
pred fstInThreadP { fst in ~t}

fact fstInThread { fstInThreadP }


fact {
	-- eventos relacionados por So estão na mesma thread
	So in ker[t]
	-- a So b_1 and ... b_m So b_m+1 ... and b_n So c then not c So a
	Acyclic[So, Event]
	-- o primeiro evento de uma thread não tem predecessor
	no fst.So
	-- um evento não pode ter mais que um sucessor
	Injective[So,Event]
}


fact allSotTotal {
	-- para todas as threads, o feixo transitivo de sua session order é uma ordem linear estrita
	all thr : Thread | Linearorder[^(sot[thr] + thr.fst->thr.fst) + id[t.thr], t.thr]
}

fact correctCommunications {
	Injective[sender,Event]
	Simple[sender,Event]
	Irreflexive[sender]
	Acyclic[So + sender,Event]
	no ker[sender] & img[sender]
}

fact {
	hb = tc[Event,So + sender]
}

-- relógios

fact {
  Bijection [clock, Event, VClock]
  all v : VClock | Entire[ v.points , Thread ]
}

fact 
{
	prev = {c1,c2 : VClock | (clock.c1).t = (clock.c2).t and isPrev [c1,c2] }
	-- c2.points[(clock.c2).t] = add[1,c1.points[(clock.c1).t]] 
	-- and (all thr : Thread -(clock.c2).t| c1.points[thr] = c2.points[thr])
	-- no fst.sender
	all c:VClock | one fst.clock.c implies isFst[clock.c]-- pode-se verificar o iff
	all thr:Thread | initial[thr.fst.clock]  -- pode-se verificar o iff
	clock . prev . ~clock = So - (sender.Event -> sender.Event)
	all e:Event | some e.sender implies isJoin[e.sender.clock, e.So.clock, e.clock]
}

-- fim de factos

--- inicio de checks
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
  all e:Event | ((some e.sender and  e.sender.t != e.t ) implies some e.sender.~fst)
}

check recvIsLast {
	all e:Event | ((some e.sender and  e.sender.t != e.t ) implies no So.e or some e.sender.~fst)
}

check reachability {
	all thr : Thread |
		t.thr <: iden & Event->Event 
			in (*(sot[thr]) + *(~(sot[thr])))
}

--- fim de checks


--- inicio de runs

run { some t1,t2 : Thread | t1 != t2 } for 4

run someSender { some sender} for 4

run any {#So >= 2} for 5

run {(some e:Event | e.sender.t != e.t and some e.sender.t) and some sender }  for exactly 6 Event,exactly 6 VClock, exactly 2 Thread

run { some e:Event | (some e.sender and  e.sender.t != e.t ) and no e.sender.~fst and some So.e }
