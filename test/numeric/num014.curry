-- Here is a rather subtle consequence of allowing polymorphic literals
-- in case expressions. The compiler used to omit default alternatives of
-- a case expression if the number of different patterns with different
-- roots is the same as the number of the data constructors of the
-- matched expression's type. However, in the example below the case
-- expression has three different cases but the default alternative is
-- not redundant at all.

data Nat = P Nat | Z | S Nat deriving (Eq,Show)

instance Num Nat where
  Z + n         = n
  S m + n@(S _) = S (m + n)
  m@(S _) + Z   = m
  S m + P n     = m + n
  P m + n@(P _) = P (m + n)
  m@(P _) + Z   = m
  P m + S n     = m + n

  m - n = m + negate n

  Z * _   = Z
  S m * n = m * n + n
  P m * n = m * n - n

  negate Z = Z
  negate (S n) = P (negate n)
  negate (P n) = S (negate n)

  abs Z       = Z
  abs n@(S _) = n
  abs (P n)   = S (negate n)

  signum Z     = Z
  signum (S _) = S Z
  signum (P _) = P Z

  fromInteger n = if n >= 0 then fromPos n else P (fromNeg (n + 1))
    where fromPos n = if n == 0 then Z else S (fromPos (n - 1))
          fromNeg n = if n == 0 then Z else P (fromNeg (n + 1))


fib n =
  case n of
    0       -> 1
    1       -> 1
    S (S n) -> fib n + fib (S n)
    _       -> 0

main = print (map fib [-1,3,9])
