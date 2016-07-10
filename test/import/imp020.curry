-- This quite contrived example checks that hidden super classes and
-- their instances are exported correctly. Incidentally, this example
-- also shows how one can define closed classes in Curry (and Haskell),
-- which can be instantiated only for a fixed set of types. Here, one can
-- only define an Int instance of A.C because its super class A.D is
-- private to A and A defines only an instance of A.D for type Int.

import A

instance C Int

main = print (f x) where x :: Int; x free
