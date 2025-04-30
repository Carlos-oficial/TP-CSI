#import "aop_lib.typ" :*
#import "commute.typ" :*

= Modeling
There are Events and Threads. 
Event may be Communications which may (only) be Sends or Receives.

There is a predecessor relation in each Thread's events


#figure(
commutative-diagram(  
  node((0, 0), $"Event"$,"tl"),
  node((0, 1), $"Event"$, "tr"),
  node((1, 0), $"Thread"$, "bl"),
  node((1, 1), $"Thread"$, "br"),
  arr("tr", "tl", $"so"$),
  arr("tr", "br", $tau$),
  arr("tl", "bl", $tau$),
  arr("br", "bl", $not id$),
  ))

