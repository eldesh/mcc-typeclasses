-- This is just another variant of an example that is due to Mark Jones'
-- Typing Haskell in Haskell paper and tests a borderline case of
-- polymorphic recursion. Whether the definition of main below is
-- accepted depends on the way how explicitly typed declarations are
-- handled in a group of mutually recursive declarations. If type
-- inference is applied to all declarations of a minimal recursive
-- declaration group, the code below is rejected because g's type is
-- monomorphic within its own declaration group and the application g
-- True inside f therefore fixes g's argument type to Bool. If, on the
-- other hand, types are inferred for the implicitly typed declarations
-- of a minimal recursive declaration group first and the explicitly
-- typed declarations are then checked with the generalized types of the
-- implicitly typed declarations, the type Ord a => a -> Bool is inferred
-- for g and therefore the code below is accepted.

main = g ()
  where f :: Eq a => a -> Bool
	f x = (x==x) || g True
	g y = (y<=y) || f True
