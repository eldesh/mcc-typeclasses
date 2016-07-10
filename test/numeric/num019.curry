-- This example tests whether the compiler correctly handles numeric
-- literals with type Char in patterns. The problem is that case
-- expressions with Char patterns normally are translated into efficient
-- switch statements. However, if characters and numbers are mixed in
-- pattern, the compiler must use fromInteger (or fromRational) to
-- convert the numbers into characters and a less efficient if-then-else
-- cascade. Fortunately, such code will rarely occur in practice.

import Ratio

-- NB deliberately incomplete instance
instance Num Char where
  x + y = chr (ord x + ord y)
  x - y = chr (ord x - ord y)
  x * y = chr (ord x * ord y)
  fromInteger i = chr (fromInteger i)

-- NB deliberately incomplete instance
instance Fractional Char where
  fromRational r | denominator r == 1 = fromInteger (numerator r)

-- first test case: mixing integer numbers and characters
-- note that ord 'a' == 97 and ord 'b' == 98 and the patterns are chosen
-- deliberately to overlap
f c =
  case c of
    97 -> True
    'a' -> False
    'b' -> True
    98 -> False

-- second test case: mixing rational numbers and characters
-- note that due to the definition of fromRational above, the last case
-- of the pattern will always fail.
g c =
  case c of
    97.0 -> True
    'a' -> False
    'b' -> True
    98.0 -> True
    97.5 -> False

-- main test program
main =
  do
    print (map f "ab")
    print (map g "ab")
    print (findall (\xs -> xs =:= map g "abc"))
