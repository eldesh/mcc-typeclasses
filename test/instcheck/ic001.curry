-- Example copied from Sect. 4.3.2 of the revised Haskell'98 report
class Foo a
class Foo a => Bar a where

instance (Eq a, Show a) => Foo [a] where
instance Num a => Bar [a]
