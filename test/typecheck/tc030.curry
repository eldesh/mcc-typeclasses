-- This example shows that only some functions in a group of
-- mutually recursive declarations can have ambiguous types.
-- The type signature for f1 is commented out deliberately.
-- Thus, a Num a1 and Ord a1 constraint appears in the
-- context of f2, where a1 is the (monomorphic) type variable
-- that is assigned to f1's argument and result type during
-- type inference of the binding group containing f1 and f2.
-- The compiler must use default resolution in order to fix
-- the type variable a1 to the default type Int within f2.
-- It might do so for the whole declaration group thus giving
-- type [Int] -> [Int] to f1, but MCC's type inferencer in fact
-- assigns the more general type (Num a, Ord a) => [a] -> [a]
-- to f1.

main = print (f1 [1,2,3])
  where --f1 :: Real a => [a] -> [a]
        f1 [] = []
        f1 (x:xs) = if x >= 0 || f2 1 then x : f1 xs else []

        f2 :: Real b => b -> Bool
        f2 x = x <= 0 || f2 (length (f1 []))
