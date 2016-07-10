-- This test checks that hidden default methods can be used in a
-- client module. Function zero calls a method of class Z (which
-- has a default implementation). Since Z has no other methods,
-- the instance declaration itself is empty

import A

instance Z Integer

main = zero
