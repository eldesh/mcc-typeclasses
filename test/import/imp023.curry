-- This example checks that an instance is exported along with its class
-- if the type is defined in another module. In particular, module C
-- exports the class C defined in module B, but not the type T defined in
-- module A. (See also imp024.curry for a variant of this example.)

import A
import C

main = doSolve (f T)
