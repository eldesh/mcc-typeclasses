-- This example uses lists to represent (positive) numbers by the length
-- of the list. However, the list type cannot be made the default numeric
-- type without restricting its argument type because of the Eq and Show
-- constraints on this type (see also num007.curry and num009.curry).

default ([a])

instance (Eq a,Show a) => Num [a] where
  fromInt n
    | n > 0 = let x free in x : fromInt (n - 1)
    | otherwise = []

  (+) = (++)

  xs     - []     = xs
  (_:xs) - (_:ys) = xs - ys

  -- (*) left as an exercise

  negate [] = []

  abs = id

  signum []    = []
  signum (x:_) = [x]

main = print (fromInt 10)
