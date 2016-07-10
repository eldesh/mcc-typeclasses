-- This is example checks whether constraints on existentially quantified
-- variables are exported correctly. (See also ex012.curry for a variant
-- of this test using universally quantified variables.)

import A

instance Show U where
  showsPrec p (U x) = showsPrec p x

main = mapM_ print [U (), U "", U False]
