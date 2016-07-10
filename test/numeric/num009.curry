-- This example uses lists to represent (positive) numbers by the length
-- of the list. Since the type [a] cannot be made the default numeric
-- type due to the Eq a and Show a constraints required by its instance
-- declaration, we use a concrete list instance type as default numeric
-- type. Using () for the argument type has the advantage that the free
-- variables introduced by fromInt can be instantiated deterministically.
-- Thus, the main goal will actually print a list of 10 () constructors.
-- If we had used default ([Bool]), the evaluation of the main function
-- would fail with a ``cannot duplicate the world'' error message and if
-- we had used default ([Int]), the evaluation of the main function would
-- flounder. (See also num007.curry and num008.curry.)

default ([()])

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
