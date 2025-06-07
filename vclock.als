module VecClocks

open RelCalc 
open World

sig VClock {
	event : one Event,
	points : Thread -> one Int,
	prev: set VClock,
	r: set VClock

}

fact event_clock_bijection {
	Bijection[event, Clock, Event]
}

pred initial [r:VClock]{
  all n:Thread | r.points[n] = 0
}

pred isJoin[ c1, c2, r: VClock] {
  all thr: Thread |
    r.points[thr] =
      (thr = (clock.r).t =>
        (maxInt[c1.points[thr], c2.points[thr]]).add[1]
      else 
        maxInt[c1.points[thr], c2.points[thr]])
}

pred gte[c1 : VClock, c2 : VClock] 
{
	all t : Thread | c1.points[t] >=  c2.points[t]
}

pred isPrev[c1 : VClock, c2 : VClock] 
{
	add[1,c1.points[(clock.c1).t]]  = c2.points[(clock.c1).t]
}

pred points_entire {
  all v : VClock | Entire[ v.points , Thread ]
}

fact 
{
	points_entire 
	prev = {c1,c2 : VClock | (clock.c1).t = (clock.c2).t and isPrev [c1,c2] }
	-- c2.points[(clock.c2).t] = add[1,c1.points[(clock.c1).t]] 
	-- and (all thr : Thread -(clock.c2).t| c1.points[thr] = c2.points[thr])
	-- no fst.sender
	all c:VClock | one fst.clock.c implies isFst[clock.c]-- pode-se verificar o iff
	all thr:Thread | initial[thr.fst.clock]  -- pode-se verificar o iff
	clock . prev . ~clock = So - (sender.Event -> sender.Event)
	all e:Event | some e.sender implies isJoin[e.sender.clock, e.So.clock, e.clock]
}

run {} for 5
