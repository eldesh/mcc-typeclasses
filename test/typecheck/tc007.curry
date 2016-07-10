-- This example is derived from an example in Mark Jones' Typing
-- Haskell in Haskell paper
-- The compiler should infer types (Eq a,Ord b) => a -> b -> Bool and
-- (Ord a,Eq b) => a -> b -> Bool for f and g, respectively.
f x z = (x==x) || g z undefined
g y z = (y<=y) || f z undefined
