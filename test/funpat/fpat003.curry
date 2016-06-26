-- This very contrived example tests that evaluation to normal form
-- occurs only when a variable is bound more than once, regardless of
-- the number of occurrences in the pattern

-- NB The normal forms of pat1 x y and pat2 x y are (x,y) and (x,x),
--    respectively
pat1 x y = (const const x x y, const y x)
pat2 x y = (const const x x y, const x y)

f1 (pat1 _ _) = success
f2 (pat2 _ _) = success

goal1 x | f1 (failed,failed) = x =:= ()
goal2 x | f2 (unknown,failed) = x =:= ()
goal3 x | f2 (failed,unknown) = x =:= ()
