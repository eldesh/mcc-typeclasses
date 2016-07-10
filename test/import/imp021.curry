-- This example checks that instances of private classes that appear in
-- the contexts of other declarations are correctly exported. In this
-- particular example, the class method f is used at type Maybe Int,
-- which uses the Maybe instance of the public class C, which in turn
-- uses the Int instance of the private class D.

import A

main = print (f (Just x)) where x :: Int; x free
