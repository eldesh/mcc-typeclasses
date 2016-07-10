-- Basic test for polymorphic methods, a constrained polymorphic
-- method, a monomorphic instance of the class, plus a function
-- that uses it (at two different types).

class C a where
  f :: Eq b => a -> b -> a

instance C Int where
  f x y | y == y = x

main = print (f zero False,f zero 'a')
  where zero = 0 :: Int

