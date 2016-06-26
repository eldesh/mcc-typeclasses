-- Pattern matching in case expressions is supposed to match alternatives
-- from top to bottom and patterns in alternatives from left to right.
-- In the example below this strategy means that the compiler must look
-- at the second alternative even though its pattern is subsumed by the
-- pattern of the first alternative and hence its right hand side can
-- never be selected. However, the pattern forces evaluation of the first
-- element of the pair to a ground term and hence makes a difference when
-- the first element is a free variable or an undefined value.
-- NB This example is due to Georgios Karachalias, Tom Schrijvers,
-- Dimitrios Vytiniotis and Simon Peyton Jones. GADTs meet their match:
-- pattern-matching warnings that account for GADTs, guards, and
-- laziness. ICFP'15.

f x y =
  case (x,y) of
    (_,False) -> 1
    (True,False) -> 2
    _ -> 3

goal1 = f undefined False
goal2 = f True True
goal3 = f _ True
goal4 = f undefined True
