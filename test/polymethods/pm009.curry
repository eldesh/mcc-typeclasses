-- Basic test for polymorphic methods, a constrained polymorphic
-- function with a default implementation, plus a function that
-- uses it (at two different types).

class C a where
  f :: Eq b => a -> b -> a
  f x y | y == y = x

-- test :: C a => a -> (a,a)
test x = (f x False,f x 'a')
