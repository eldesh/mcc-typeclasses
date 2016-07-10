-- This test checks that the compiler correctly reports conflicts
-- between global and local fixity declarations for class methods

infix 4 ===

class Equal a where
  infix 4 ===
  (===) :: a -> a -> Bool
