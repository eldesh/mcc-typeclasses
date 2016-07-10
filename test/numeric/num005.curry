-- Haskell's default rules are quite restrictive. In particular,
-- Sect. 4.3.4 mandates that an ambiguous type can be defaulted
-- if it occurs only in constraints of the form C u, where u is
-- a type variable, and the classes in those constraints are all
-- drawn from the classes in the Prelude and the standard libraries.
-- MCC implements neither of these restrictions. Therefore, the
-- following program is accepted by MCC, but not by a (standard
-- compliant) Haskell compiler. (See num006.curry for a test for
-- deriving with constraints that are not of the form C u.)

class Num a => C a where
  -- stupid method, just present in order to enforce C constraints
  identity :: a -> a
  identity x = x

instance C Integer
instance C Float

main = print (identity 42)
