-- The following is a rather contrived example involving a pattern
-- declaration in a mutually recursive declaration group. The type of
-- the pattern variable nil is not generalized (even though it were
-- sound in this case) and therefore f is not polymorphic in its first
-- argument. However, this example was accepted once by the compiler
-- due to an incorrect test in TypeCheck.tcDeclGroup.
main = (f [0::Int] 0,f "a" "a")
  where (nil,_) = ([],f)
        f x y | x /= nil = y
