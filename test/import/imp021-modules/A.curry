module A(C(..)) where

class C a where
  f :: a -> a

class D a where
  g :: a -> Bool

instance D Int where
  g 0 = True

instance D a => C (Maybe a) where
  f (Just x) | g x = Just x
  f Nothing = Nothing
