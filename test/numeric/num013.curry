-- Literals in equation heads (as well as in fcase alternatives) are not
-- polymorphic, i.e., one cannot mix them with data constructors of a
-- numeric type. The rationale behind this restriction is that the
-- interpretation of an expression
--   fcase n of { 0 -> True; 1 -> False; S (S n) -> even n }
-- is ambiguous in general. It could either denote the expression
--   fcase n of { n | n=:=0 -> True; n | n=:=1 -> False; S (S n) -> even n }
-- which is evaluated with a non-deterministic choice when n is a number,
-- or the expression
--   if n==0 then True
--   else if n==1 then False
--   else fcase n of { S (S n) -> even n }
-- which suspends when n is a free variable (cf. num012.curry and
-- num013.curry for variants of this example).

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

even 0 = True
even 1 = False
even (S (S n)) = even n
main = print (filter even [1..4])
