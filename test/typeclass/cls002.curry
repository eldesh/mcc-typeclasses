class A a where
  f :: a -> a
class A a => B a where
  g :: a -> a
  g = f

instance A Integer where
  f x = x
instance A Float where
  f _ = 0.0
instance A a => A (Maybe a) where
  f (Just x) = Just (f x)
  f Nothing = Nothing

-- NB The (A a) context is required by the super class instance
instance A a => B (Maybe a) where

main = (g (Just 1),g (Just 1.0))
