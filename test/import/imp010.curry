-- This test checks that A's interface is imported correctly even though
-- it contains a definition for A.Bool and Prelude.Bool whose unqualified
-- name is the identical. The key point here is that Prelude.Bool is
-- hidden in A's interface and thus must not be imported into this
-- module.

import Prelude hiding(Bool)
import A

true,false :: Bool
true = True
false = False
