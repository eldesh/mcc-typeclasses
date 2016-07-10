module A where

class C a where
  f :: a -> Success

data T = T

instance C T where
  f T = success
