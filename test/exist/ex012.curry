-- This is example checks whether constraints on universally quantified
-- variables are exported correctly if they occur on the right hand side
-- of a type declaration. Note that Show instance does not have a Show a
-- context. This demonstrates the difference between left and right hand
-- side contexts (cf. also ex011.curry).

import A

instance Show (U a) where
  showsPrec p (U x) = showsPrec p x

main = print (U ()) >> print (U "") >> print (U False)
