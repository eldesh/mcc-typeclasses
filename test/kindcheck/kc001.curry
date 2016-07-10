-- This example comes from Sect. 4.6 of the Haskell'98 report
-- (see also kc004.curry for a sligthly more elaborate variant
-- of this example).

data C a => D a = Foo (S a)
type S a = [D a]
class C a where
  bar :: a -> D a -> Bool
