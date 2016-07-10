module A where

class C a where
  infix 6 `op`
  -- NB precedence deliberately chosen so that it binds tighter than (:)
  op :: a -> a -> a
