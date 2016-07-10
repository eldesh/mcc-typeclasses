-- This example fails because (derived) instance contexts are
-- restricted to assertions of the form C u, where u is a type
-- variable, yet T's Eq instance would require (Eq (f a)). See
-- der003.curry for an example that gives a rationale for this
-- restriction. See also ../typeclass/cls009.curry, which checks
-- that an explicit instance cannot be declared either.

data T f a = T (f a) deriving (Eq)
