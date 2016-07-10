-- This example is derived from an example in Mark Jones' Typing
-- Haskell in Haskell paper
-- The type signatures for f and g are the ones that the compiler
-- would infer for the two functions. Nevertheless, this program
-- is (necessarily) rejected by the compiler. The problem is that
-- the compiler cannot resolve the Eq b and Ord b constraints for
-- the second argument (undefined) of g and f, respectively, in
-- the recursive calls in the right argument of (||) because it
-- introduces fresh instances of f and g's type signatures for
-- typing these arguments. If the type signatures are omitted,
-- the compiler uses the same type variables for typing the left
-- and right hand sides of the two equations and will infer that
-- in both equations, the undefined expression is used at the same
-- type as the first argument of the equation.

f :: (Eq a,Ord b) => a -> b -> Bool
g :: (Ord a,Eq b) => a -> b -> Bool
f x z = (x==x) || g z undefined
g y z = (y<=y) || f z undefined
