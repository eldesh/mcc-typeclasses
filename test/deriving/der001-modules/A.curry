-- This module checks that instances can be derived even if (almost)
-- no Prelude entities are in scope.

module A where
import Prelude(Eq,Ord,Enum,Bounded,Show)

data Coin = Zero | One deriving (Eq,Ord,Enum,Bounded,Show)
