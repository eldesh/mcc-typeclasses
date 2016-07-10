-- Basic test for polymorphic methods, a simple polymorphic function
-- plus a function that uses it (at two different types).

class C a where
  f :: a -> b

--test :: C a => a -> (b,c)
test x = (f x,f x)
