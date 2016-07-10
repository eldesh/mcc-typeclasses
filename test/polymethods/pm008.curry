-- Basic test for polymorphic methods, a constrained polymorphic
-- function, plus a function that uses it (at two different types).

class C a where
  f :: Eq b => a -> b -> a

-- test :: C a => a -> (a,a)
test x = (f x False,f x 'a')
