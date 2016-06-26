-- The examples below test function patterns in rigid case expressions.
-- Note that function patterns are similar to irrefutable (aka lazy)
-- patterns in that a rule with a function pattern always matches and the
-- remaining alternatives are never checked unless the rule has a guarded
-- right hand side and all of its guards fail.

f xs =
  case xs of
    _ ++ [x] ++ _ -> x
    _ -> 0

g xs =
  case xs of
    _ ++ [x] ++ _ | x > 0 -> x
    _ -> 0

h xs =
  case xs of
    _ ++ [x] ++ _ | x > 0 -> x | otherwise -> 0
    _ -> -1
    
goal1 = f [1..3]
goal2 = f []
goal3 = f _
goal4 = g [-1..1]
goal5 = g []
goal6 = h [-1..1]
goal7 = h []
goal8 = case _ of (id x) -> x
goal9 = let x,xs free in case (x:xs) of id [1,2,3] -> (x,xs)
