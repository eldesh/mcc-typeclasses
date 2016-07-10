-- A rather contrived test for deriving in the presence of right hand
-- side constraints for universally quantified type variables, which
-- shows that things are not as simple as it seems. In contrast to the
-- example in der006.curry, where the Eq a context for the Eq (U a)
-- instance could be omitted, it is necessary in this example.

data U a = L a | Eq a => R a deriving (Eq,Ord)

f :: U a -> U a -> Bool
f u1 u2 = u1 == u2
