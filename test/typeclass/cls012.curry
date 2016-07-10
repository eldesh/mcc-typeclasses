-- Only constraints of the form C u are allowed instance declaration contexts
-- This applies to derived declarations, too.

data T f = T (f Int) deriving (Eq)
