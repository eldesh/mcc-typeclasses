-- This is a simple test that demonstrates why the pattern binding
-- update strategy implemented in MCC is useful. If x were not updated
-- after xs has been evaluted, the lazy application of the
-- corresponding projection function would retain a reference to the
-- long list, which means that the program will run out of memory with
-- MCC's default heap size.
-- Note: This example assumes that the compiler does not use a demand
-- analysis in order to transform the pattern binding into a more
-- efficient case expression.

import List(last)

main = print (last xs + x)
  where (x:xs) = [1..250000]
