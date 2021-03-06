-- This is a rather contrived example that shows that polymorphic numeric
-- literals allow mixing numbers and data constructors in a single case
-- expression (cf. num012.curry and num013.curry for variants of this
-- example).

import Prelude hiding(even)

data Nat = Z | S Nat deriving (Eq,Show)

instance Enum Nat where
  succ n = S n
  pred (S n) = n
  fromEnum Z = 0
  fromEnum (S n) = 1 + fromEnum n
  toEnum n
    | n > 0  = S (toEnum (n - 1))
    | n == 0 = Z

instance Num Nat where
  Z   + n = n
  S m + n = S (m + n)
  n   - Z   = n
  S m - S n = m - n
  -- (*), abs, signum omitted because they are not used
  fromInteger n
    | n >  0 = S (fromInteger (n - 1))
    | n == 0 = Z

even n = case n of { 0 -> True; 1 -> False; S (S n) -> even n }
main = print (filter even [1..4])
