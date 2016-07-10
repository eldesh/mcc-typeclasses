-- Basic test for polymorphic methods, a constrained polymorphic
-- method with multiple constraints, a polymorphich instance of
-- the class instance constraints, plus a function that uses it
-- (at two different types).

class C a where
  -- NB constrained type variable is not the first one
  f :: (Num b, Ord b) => b -> a -> a -> a
  f x y z = if x >= 0 then y else z

instance C Bool where
instance C Char where
  f x y z = if x >= fromInt (ord z) then y else z

instance (C a,C b) => C (a,b) where
  f x (y1,y2) (z1,z2) = (f x y1 z1, f x y2 z2)

main = print [f 0 a b, f (-1.0) a b]
 where a = (False,'a')
       b = (True,'b')

