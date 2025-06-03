module VecClocks

open RelCalc 


sig Node {
	clock : one VClock
}

sig VClock {
	points : Node -> one Int
}

fact {
  Bijection [clock, Node, VClock]
  all v : VClock | Entire[ v.points , Node]
}

fun init [] : VClock {
  { r: VClock | all n:Node | r.points[n] = 0}
}

fun join[c1 : VClock, c2 : VClock]: VClock {
  { r: VClock |
    all n: Node |
      r.points[n] = (c1.points[n] >= c2.points[n] => c1.points[n] else c2.points[n])
  }
}

fun inc[n:Node, c : VClock]: Node->Int {
 { n_ : Node, i : Int | i = (n_ = n =>  add[ c.points[n_], 1] else c.points[n_])  }
}

run {}
