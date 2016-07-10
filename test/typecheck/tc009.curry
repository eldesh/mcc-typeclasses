-- This example is from Sect 4.5.2 of the Haskell report
-- The compiler should infer type (Ord a, Show a) => a -> a -> String
-- for both g1 and g2.
g1 x y = if x>y then show x else g2 y x
g2 p q = g1 q p
