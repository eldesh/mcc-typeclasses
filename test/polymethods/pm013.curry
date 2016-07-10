-- Method contexts must not restrict the type variable which appears in
-- the type class declaration (cf. Sect. 4.3.1 of the Haskell report).

class C a where
  f :: Eq a => a -> a
  f x | x == x = x
