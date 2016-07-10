-- This example checks that an overloaded function is called with the
-- correct dictionary when using a variable with a constrained type
-- (that default to an Int in this case)

f (0:xs) = shows xs ""

main = putStrLn $ f [0..2]
