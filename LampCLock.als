module LampClocks

open RelCalc 
open World

sig LClock {
	event : one Event,
	int points : set Thread,
	prev: set LClock,
	ord: set LClock

}

fact event_clock_bijection {
	Bijection[event, LClock, Event]
}

pred initial [r:LClock]{
	r ; points :> (Thread - r.event.t) = 0 ** (Thread - r.event.t)
	r ; points :> (r.event.t)          = 1 ** (r.event.t)
}

pred isPrev[c1 : LClock, c2 : LClock] 
{	
	c1.event.t = c2.event.t
	c1 ; points = c2 ; points fun/add (c1.event.t.fst.~event) ; points
}

pred fst_is_init {
	all c : event.(Thread.fst) | initial[c]
}

pred points_entire {
	id[Thread] in ~points ; points
}



pred isJoin[ c1, c2, r: LClock] {
	r ; points = (c1 ; points + c2 ; points) fun/add (r.event.t.fst.~event) ; points
}

fact 
{
	points_entire 
	fst_is_init
	
	prev = event.((Event - Rcv) <: So).~event
	prev in {c1,c2 : LClock | isPrev [c1,c2]} 

	all e:Rcv | isJoin[e.sender.~event, e.So.~event, e.~event]
}


run {some sender - ker[t] } for exactly 2 Thread, exactly 6 Event,exactly 6 LClock

fact ord_def {
	ord = {c1,c2 : LClock | c1 < c2 }
}

check clock_hb_galois_conection {
	ord in event.hb.~event
} for 5
