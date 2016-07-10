-- Basic test for polymorphic methods, a simple polymorphic function
-- plus a function that uses it (at two different types).

class C a where
  -- NB type class variable does not appear first in the method's type
  f :: b -> a

--test :: C a => (a,b) -> [c]
test x y = [f x,f y]
