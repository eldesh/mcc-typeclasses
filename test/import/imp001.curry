-- This example checks that for the data constructors of a type in an
-- export list, it does not matter whether the constructors are imported
-- from the same module as their, nor whether these names are
-- ambiguous.

module imp001(B.T(L,R)) where
import qualified B(T)
import qualified C(T(L))
import qualified D(T(R))

data LR = L | R
