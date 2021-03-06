-- Basic test for polymorphic methods, a simple polymorphic function,
-- a polymorphic instance of the class (with instance constraints),
-- plus a function that uses it (at two different types).

class C a where
  f :: a -> b

instance C Int where
  f _ = x where x free
instance C Float where
  f _ = x where x free

instance (C a, C b) => C (a,b) where
  f (x,y) | f x =:= f y = z where z free

main = doSolve (a =:= False & b =:= 'a') >> print (a,b)
  where a = f zero; b = f zero
        zero = (0::Int,0::Float)
