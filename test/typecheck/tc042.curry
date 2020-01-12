-- Each field label in a data or renaming type introduces a selector
-- function with the same name, which extracts the respective component
-- from the argument. The type of any selector function should include
-- only those (left hand side) type constraints from the type declaration
-- that are relevant for the data constructors where the respective field
-- label is used.

data (Eq a, Eq b, Eq c) => T a b c
 = (Show a, Show b, Show c) => C1{ left :: a, common :: b }
 | (Show a, Show b, Show c) => C2{ common :: b, right :: c }

l = left
r = right
c = common


newtype (Eq a, Eq b) => N a b = N{ new :: b }
n = new
