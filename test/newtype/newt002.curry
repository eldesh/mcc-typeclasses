-- This contrived example uses a renaming type that expands into a cyclic
-- type synonym after removal of newtype constructors. Of course, since
-- this type is inhabited only by bottom it is not very useful.

newtype Inf a = Inf (Inf a) deriving (Eq,Show)
instance Functor Inf where
  fmap f (Inf x) = Inf (fmap f x)
instance Monad Inf where
  return x = Inf (return x)
  Inf x >>= f = Inf (x >>= f)

incrInf (Inf x) = fmap (1 +) (Inf x)
