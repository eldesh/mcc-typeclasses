module A where

class C a where
  infix 4 `op`
  op :: a -> a -> a
