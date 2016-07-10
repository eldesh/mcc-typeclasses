-- The following program should be rejected by the type checker

class A a where
  f :: a -> a
class A a => B a where
  g :: a -> a
  g = f

instance A Int where
  f x = x
instance A Float where
  f _ = 0.0
instance A a => A (Maybe a) where
  f (Just x) = Just (f x)
  f Nothing = Nothing

-- The error is here: This instance requires an A a (or B a) context
instance B (Maybe a) where

main = g (Just 1,Just 1.0)
