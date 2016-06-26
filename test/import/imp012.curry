-- This example checks that the compiler can cope with eta-expanded
-- functions when the eta-expansion crosses a newtype and the newtype's
-- definition is not visible.

import qualified Prelude
import A

plus x y = return x >>= \x -> return y >>= \y -> return (x Prelude.+ y)
main = Prelude.print (run (plus 1 2))
