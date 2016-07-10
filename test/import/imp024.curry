-- This example checks that an instance is exported along with its type
-- if the class is defined in another module. In particular, module C
-- exports the type T defined in module B, but not the class C defined in
-- module A. (See also imp023.curry for a variant of this example.)

import A
import C

main = doSolve (f T)
