-- This rather contrived example demonstrates that it is possible to have
-- a default type with a free type variable. However, the type variable
-- must not be constrained by the type's Num instance declaration (see
-- also num008.curry and num009.curry).

default (T a)

data T a = T deriving (Eq,Show)

instance Num (T a) where
  fromInt _ = T
  T + T = T
  T - T = T
  T * T = T

  negate T = T
  abs T = T
  signum T = T

main = print (fromInt 10)
