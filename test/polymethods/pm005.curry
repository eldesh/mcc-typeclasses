-- Basic test for polymorphic methods, a simple polymorphic function,
-- a polymorphic instance of the class (with instance constraints),
-- plus a function that uses it (at two different types). Also uses
-- a default method implementation

class C a where
  f :: a -> b
  f _ = x where x free

instance C Int where
instance C Float where

instance (C a, C b) => C (a,b) where
  f (x,y) | f x =:= f y = z where z free

main = doSolve (a =:= False & b =:= 'a') >> print (a,b)
  where a = f zero; b = f zero
        zero = (0::Int,0::Float)
