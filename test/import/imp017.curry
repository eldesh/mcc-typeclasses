-- This module implements another test that method names are in scope
-- in the left hand side of an instance declaration even if the method
-- name itself is imported from another module or ambiguous.

import qualified Prelude
import A(Eq)
import qualified B((==))

(==) :: Prelude.Int -> Prelude.Int -> Prelude.Bool
(==) = (Prelude.==)

data T = C
instance Eq T where
  C == C = Prelude.True
