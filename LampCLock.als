module LampClocks

open RelCalc 
open World

sig Singl {}

fact {one Singl}

sig LClock {
	event : one Event,
	int point : Singl,
	ord: set LClock

}


fact ord_def {
	ord = {c1,c2 : LClock | c1 ; point < c2 ; point  }
}


fact event_clock_bijection {
	Bijection[event, LClock, Event]
}

pred initial [r:LClock]{
	r ; point  = 1 ** Singl
}

pred fst_is_init {
	all c : event.(Thread.fst) | initial[c]
}

pred isPrev[c1 : LClock, c2 : LClock] 
{	
	c2 ; point = c1 ; point fun/add 1 ** Singl
}

pred isJoin[ c1, c2, r: LClock] {
	r ; point = (c1 ; point + c2 ; point) fun/add 1 ** Singl
}

fact 
{
	fst_is_init
	
	all e:Event - Rcv | isPrev[event.(e.So), event.e]
	all e:Rcv | isJoin[e.sender.~event, e.So.~event, e.~event]
}

run {some sender - ker[t]}

check clock_hb_ord_galois_conection {
	event.hb.~event in ~ord 
}

check clock_ord_hb_galois_conection_ShouldFail {
	~ord in event.hb.~event
}
