-- This example is due to Mark Jones' Typing Haskell in Haskell paper
-- This variant should be rejected by a Haskell compiler due the last
-- sentence in Sect. 4.5.2 of the Haskell 98 report:
--  "If the programmer supplies explicit type signatures for more than
--   one variable in a declaration group, the contexts of these
--   signatures must be identical up to renaming of the type variables."
-- However, as Mark Jones already notes in the THiH paper, this
-- restriction is not necessary and therefore the example below should
-- be accepted by MCC. (Obviously, replacing Eq a by Ord a in f's
-- definition will make the example type check in Haskell as well.)
-- (See also tc038.curry for a variant of this example.)
f :: Eq a => a -> Bool
g :: Ord a => a -> Bool
f x = (x==x) || g True
g y = (y<=y) || f True
