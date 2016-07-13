module A where

class C a where
  f :: a -> Bool

data T = T

instance C T where
  f T = True
