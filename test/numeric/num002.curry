-- This example demonstrates the interaction of overloaded numeric
-- literals in patterns with type class constraints.
-- The compiler should report an error detecting either missing
-- Integral Float or Fractional Int instance for the body of f.
f [0,x] = (x `div` 1,x / 1)
