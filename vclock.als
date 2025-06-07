module VecClocks

open util/integer

open RelCalc 
open World



sig VClock {
	event : one Event,
	points : Thread -> one Int,
	prev: set VClock,
	r: set VClock

}

fact event_clock_bijection {
	Bijection[event, VClock, Event]
}

pred initial [r:VClock]{
  all n:Thread | r.points[n] = (n=r.event.t => 1 else 0)
}

pred isJoin[ c1, c2, r: VClock] {
  all thr: Thread |
    r.points[thr] =
      (thr = r.event.t =>
        (larger[c1.points[thr], c2.points[thr]]).add[1]
      else 
         larger[c1.points[thr], c2.points[thr]])
}

pred gte[c1 : VClock, c2 : VClock] 
{
	all t : Thread | c1.points[t] >=  c2.points[t]
}

pred gt[c1 : VClock, c2 : VClock] 
{
	all t : Thread | c1.points[t] >  c2.points[t]
}


pred isPrev[c1 : VClock, c2 : VClock] 
{	
	-- c1.event not in Rcv
	c1.event.t = c2.event.t
	add[1,c1.points[c1.event.t]]  = c2.points[c1.event.t]
	gte[c2 , c1]
	-- c1.points - (c1.event.t <: c1.points) in c2.points
}

pred points_entire {
  all v : VClock | Entire[ v.points , Thread ]
}

pred fst_is_init {
	all c : event.(Thread.fst) | initial[c]
}

fact 
{
	points_entire 
	fst_is_init
	
	prev = event.((Event - Rcv) <: So).~event
	prev = {c1,c2 : VClock | isPrev [c1,c2]} 

	all e:Event | some e.sender implies isJoin[e.sender.~event, e.So.~event, e.~event]
}

check {
	event.hb.~event in {c1,c2:VClock|gte[c1,c2]} - id[VClock]
} for 6

run {some ~t.sender.t - id[Thread]} for exactly 6 Event,6 VClock,2 Thread
