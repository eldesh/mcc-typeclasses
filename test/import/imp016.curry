-- This check a rather obscure feature of Curry. Method names are in
-- scope on the left hand side of an instance method declaration
-- regardless of the module from which they are imported.

import qualified A(C(..))
import B(C)              -- B.zero, B.one cannot be used

-- Deliberately declare the instance for B.C whose methods cannot be
-- used in expressions
instance B.C Int where
  zero = 0
  one = 1

main = print (A.zero :: Int, A.one :: Int)

