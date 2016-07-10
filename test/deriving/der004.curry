-- This example checks that the compiler correctly derives instances
-- if some of the argument type constraints are ``hidden'' behind type
-- synonyms.

data T a = T0 | T1 (Us a) deriving (Eq,Ord)
data U a = U0 | U1 a  deriving (Eq,Ord)

type Us a = [U a]
