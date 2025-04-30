open RelCalc as r


pred order [R:Event->Event] {
	R.R in R and 
	Event->Event in R ++ ~R and 
	R & ~R in iden
}


sig Event {
	t: one Thread,
	So: lone Event,
	hb: set Event
}

abstract sig Communication extends Event {}

sig Send extends Communication {}

sig Rcv extends Communication {
	sender: one Send
}

sig Thread {}

fact {
	So in ker[t]
	// So in t.~t
	^So ++ ~^So in ker[t] - iden
	// So.So in So and 
	// t.~t in ^So ++ ~^So and
	// no ^So & iden 
	// So & ~So in iden
	sender.t in t.(Thread->Thread -iden)
	~sender.sender in iden
	hb = ^(So ++ sender)
}

fact {
	Send in Rcv.sender
}

run {} for exactly 6 Event, 2 Thread

