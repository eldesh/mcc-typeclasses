-- A very contrived example with right hand side contexts. The derived
-- Bounded instance must have an Eq a context in order to define minBound
-- and maxBound correctly.

data T a = Eq a => T a deriving Bounded

