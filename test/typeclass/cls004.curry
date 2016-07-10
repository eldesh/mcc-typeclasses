-- This test checks that fixity declarations are allowed in class
-- declarations

class Equal a where
  infix 4 ===
  (===) :: a -> a -> Bool

instance Equal Integer where
  (===) = (==)

main = 17 + 25 === 42
