module A where

class Equal a where
  infix 4 ===
  (===) :: a -> a -> Bool

  x === y | x =:= y = True
  x === y | x =/= y = False
