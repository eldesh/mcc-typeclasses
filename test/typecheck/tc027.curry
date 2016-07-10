-- This example shows that in a group of mutually recursive
-- declarations, only those constrained type variables can
-- be generalized that are free in all declarations. In
-- particular, the types inferred for decode, decodeN, and
-- decodeN' before generalization are
--   decode :: a1 -> a1
--   decodeN :: b1 -> a1 -> a1
--   decodeN' :: b1 -> a1 -> a1
-- and the inferred context is (Num a1, Num b1, Ord b1). Since
-- b1 does not appear in decode's type, this type variable must
-- not be generalized and therefore will be fixed to Integer (by the
-- default rules for numeric types). Thus, the types of decodeN
-- and decodeN' will become Integer -> a -> a and the expression
-- decodeN 0.0 0 [] is rejected because Integer is not an instance
-- of Fractional.
-- Note that ghc, hbc, and nhc98 are in fact able to lift this
-- restriction and generalize b1's type so this program is
-- accepted. This means that different dictionaries for the first
-- argument are passed to the two decodeN applications. Unfortunately,
-- this is not possible with MCC's current dictionary transformation
-- implementation.

main = print (decode [1,2,3], decodeN 1 0 [1], decodeN 1.0 0 [1])
  where decode [] = []
        decode (n:ns)
          | n == -1 = decodeN 1 0 ns
          | n == -2 = decodeN 2 0 ns
          | n == -3 = decodeN 3 0 ns
          | otherwise = n : decode ns

        decodeN m z ns
          | m > 0 = decodeN' m z ns
          | otherwise = z : decode ns
        decodeN' m z (n:ns) = decodeN (m - 1) (z + n) ns
