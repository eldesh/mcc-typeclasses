-- Here is the canonical example for existential types in Haskell. Note
-- the subtle difference between g1 on one hand and g2 and g3 on the
-- other hand. The type of g1 is Showable -> Maybe String. Type inference
-- for g2 and g3, on the other hand, fails because right hand side
-- contexts of data type declarations are ignored for lazy patterns,
-- since in general the corresponding argument may be evaluated too late
-- or even not at all. Therefore, no Show instance is in scope for the
-- skolem type of x. (See lp005.curry and lp006.curry for variants of
-- this test. Also see lp008.curry for a variant using universal
-- quantification.)

data Showable = forall a. Show a => Showable a

g1 (Showable x) = Just (show x)
--g2 ~(Showable x) = Just (show x)
g3 s = Just (show x) where Showable x = s
