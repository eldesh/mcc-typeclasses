-- This example takes Haskell's rules for importing and exporting
-- instances to the extreme. It defines a class C and a type T in
-- different modules A and B, respectively, and introduces an instance C
-- T in yet another module C. The latter module is imported into a fourth
-- module D. The main function below shows that it is sufficient to
-- import the latter module in order to use that instance (and we need
-- module B of course in order to use the type's data constructor).

import B
import D

main = doSolve (x=:=T) where x free
