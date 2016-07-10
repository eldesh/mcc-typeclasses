-- This test checks that fixity declarations inside a class are not
-- visible outside the class

x === y
  | x =:= y = True
  | x =/= y = False

class C a where
  infix 4 ===
