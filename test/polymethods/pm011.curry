-- Basic test for polymorphic methods, a constrained polymorphic
-- method with multiple constraints, a monomorphic instance of the
-- class, plus a function that uses it (at two different types).

class C a where
  -- NB constrained type variable is not the first one
  f :: (Num b, Ord b) => b -> a -> a -> a

instance C Char where
  f x y z = if x >= 0 then y else z

main = print [f 0 'a' undefined, f (-1.0) undefined 'b']


