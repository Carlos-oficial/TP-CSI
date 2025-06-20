module VecClocks

open RelCalc 
open World

sig VClock {
	event : one Event,
	int points : set Thread,
	prev: set VClock,
	r: set VClock,

	ord: set VClock

}

fact event_clock_bijection {
	Bijection[event, VClock, Event]
}

pred initial [r:VClock]{
	r ; points :> (Thread - r.event.t) = 0 ** (Thread - r.event.t)
	r ; points :> (r.event.t)          = 1 ** (r.event.t)
}

pred isPrev[c1 : VClock, c2 : VClock] 
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

pred isJoin[ c1, c2, r: VClock] {
	r ; points = (c1 ; points + c2 ; points) fun/add (r.event.t.fst.~event) ; points
}

fact 
{
	points_entire 
	fst_is_init
	
	event.((Event - Rcv) <: So).~event = {c1,c2 : VClock | isPrev [c1,c2]}

	-- prev = event.((Event - Rcv) <: So).~event 
	prev = {c1,c2 : VClock | isPrev [c1,c2]}

	all e:Rcv | isJoin[e.sender.~event, e.So.~event, e.~event]
}


run {some sender - ker[t] } for exactly 2 Thread, exactly 4 Event,exactly 4 VClock

fact ord_def {
	ord = {c1,c2 : VClock | c1 ; points < c2 ; points }
}

check clock_hb_galois_conection {
	~ord = event.hb.~event
} for 3
