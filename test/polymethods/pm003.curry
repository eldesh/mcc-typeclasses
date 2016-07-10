-- Basic test for polymorphic methods, a simple polymorphic function,
-- a polymorphic instance of the class (without additional constraints),
-- plus a function that uses it (at two different types).

class C a where
  f :: a -> b

instance C (a,b) where
  f (_,_) = x where x free

main = doSolve (a =:= False & b =:= 'a') >> print (a,b)
  where a = f zero; b = f zero
        zero = (0::Int,0::Float)
