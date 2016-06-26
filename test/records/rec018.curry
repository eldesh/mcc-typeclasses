-- This example checks that the order of import declarations is
-- irrelevant when importing a label more than once and the label is
-- imported without its type from one of the modules. Note that it is
-- unclear whether a label can be used in a record (update) expression in
-- this case or not and MCC does not allow it at present. (See also
-- ../test0017 for the obvious variant of this example.)

import B(len)
import qualified A(T(..))
f = A.C{ len=0 }
