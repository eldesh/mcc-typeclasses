-- Basic test for polymorphic methods, a simple polymorphic function,
-- a (monomorphic) instance of the class, plus a function that uses it
-- (at two different types).

class C a where
  f :: a -> b

instance C Int where
  f _ = x where x free

main = doSolve (a =:= False & b =:= 'a') >> print (a,b)
  where a = f zero; b = f zero
        zero = 0 :: Int
