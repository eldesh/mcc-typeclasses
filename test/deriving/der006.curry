-- A test for deriving in the presence of right hand side constraints for
-- universally quantified type variables. In principle, the Eq (U a)
-- instance should not require an Eq a context. However, the compiler at
-- present doesn't notice this (see also der007.curry for a variant of
-- this test).

data U a = Eq a => U a a deriving (Eq,Ord)

f :: U a -> U a -> Bool
f u1 u2 = u1 == u2
