-- This example combines function patterns with constrained variables
-- that can occur more than once

g x y z | y =/= z = (const z x,const z y)
f (g x 1 y) = [x,y]

main = f (unknown,unknown)
