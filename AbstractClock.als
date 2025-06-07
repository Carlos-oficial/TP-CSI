module AbstractClock

open RelCalc
open World

sig Clock{
	e: Event,
	ord: set Clock
}

fact {
	Bijection[e,Clock,Event]
}

fact {
	ord.e in e.hb
}

run {}
