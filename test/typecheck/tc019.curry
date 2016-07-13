-- Unresolved overloading caused constraint in explicitely typed expression
f = (undefined :: Eq a => a) >> putStr ""
