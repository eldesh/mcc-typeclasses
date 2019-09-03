-- Here is a canonical example for using right hand side constraints in a
-- data type declaration. These constraints are used to dynamically
-- provide the corresponding type class instances in the scope of the
-- data constructor. Note that this does not extend to lazy patterns.
-- (Also see tests lp005.curry, lp006.curry and lp007.curry for variants
-- that use existential quantification.)

data Showable a = Show a => Showable a

f1 (Showable x) = Just (show x)
f2 ~(Showable x) = Just (show x)
f3 s = Just (show x) where Showable x = s



