-- This program checks that instances can be derived even if no
-- Prelude entities are in scope.

import A

main = print [minBound::Coin .. maxBound]
