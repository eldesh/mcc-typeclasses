module A(C(..)) where

class D a where
  g :: a -> Success

class D a => C a where
  f :: a -> a
  f x | g x = x

instance D Int where
  g 0 = success
