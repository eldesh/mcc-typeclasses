-- MCC's simplifier uses compile time beta-reduction only in a few
-- places. One is that let x = e in x, where x is not free in e, is
-- replaced by e. This example allows checking that type annotations
-- in the syntax tree are updated properly when x has a polymorphic
-- type. Note that it is important that the binding of x is a partial
-- application (since constants and plain variables are always
-- substituted) and a non-expansive expression (otherwise x's type
-- wouldn't be generalized).
main = let x = asTypeOf [] in x
  where asTypeOf :: a -> a -> a
  	asTypeOf _ x = x
