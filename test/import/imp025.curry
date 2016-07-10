-- This example shows that an instance declaration must be exported along
-- with the class or with the type alone even if the class and the type
-- are defined in the same module. The point is that module B exports
-- only type T from module A and module C exports only class C from A.
-- Nevertheless, the C T instance also defined in A must be imported into
-- this module.

import B
import C

main = doSolve (f T)
