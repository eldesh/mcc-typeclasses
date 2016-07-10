-- This is a simple test that shows that numeric literals in case
-- expressions have a polymorphic type.

data Nat = Z | S Nat deriving (Eq,Show)
instance Num Nat where
  -- we leave out all methods except fromInteger because they are not
  -- used in the test
  fromInteger n = if n == 0 then Z else S (fromInteger (n - 1))

zero n = case n of { 0 -> True; _ -> False }

main = print (zero Z && zero 0 && zero 0.0)
