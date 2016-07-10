-- This is another variant of tc034.curry and tc035.curry.
-- Assuming that g's inferred type is
--   Eq (_f b) => (a -> b) -> Bool
-- (see tc034.curry for a discussion of that type), the type that is
-- inferred for f is
--   (Functor f, Eq (f (b -> b))) => f a -> Bool
-- The type of g is accepted by the compiler because the apparently
-- ambiguous type variable _f is bound in the type environment (namely
-- in the type of f's argument xs). In contrast, the type variable b
-- in f's type is really ambiguous.
-- Incidentally, there is a good reason for not reporting an error
-- for f's definition, but rather for the application of f. For instance
-- in the following -- admittedly contrived -- code
--   data Taut a = Taut
--   instance Eq (Taut a) where Taut == Taut = True
--   main = f Taut
-- the use of f is unproblematic because the equality instance of Taut
-- does not depend on its argument type at all and therefore it does
-- not matter that the type variable b is ambiguous.

f xs = g (const id)
  where g h = fmap h xs == fmap h xs

main = f "abc"
