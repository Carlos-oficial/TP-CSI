module AbstractClock

open RelCalc
open World

sig Clock{
	e: Event,
	ord: set Clock,

	repr: univ
}

fact {
	Bijection[e,Clock,Event]
}

fact {
	ord.e in e.hb
}

{ 
	-- initial events are incomparable
	-- session order in clock order
	-- only sends exchenge causal context
}

run {}
