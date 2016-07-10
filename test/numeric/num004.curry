-- This example checks that an instance method is called with the
-- correct dictionary when using a variable with a constrained type
-- (that default to an Int in this case)

f (0:xs) = xs!!0 + xs!!1

main = print $ f [0..2]
