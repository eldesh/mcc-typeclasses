-- This is a very obscure case where the compiler may infer an
-- ambiguous type for a top-level function. In particular, the
-- type inferred for decode is (Num a1, Ord a1, Num a) => a -> a.
-- This means that decode cannot be used at all (outside of its
-- declaration) group. For instance, an error would be reported
-- if the main function is uncommented. Interestingly, no error
-- would be reported if a type signature is given for decodeN or
-- decodeN'. In that case, the first argument of decodeN in the
-- three calls inside decode would be assigned type Integer by the
-- default rules.

decode [] = []
decode (n:ns)
  | n == -1 = decodeN 1 0 ns
  | n == -2 = decodeN 2 0 ns
  | n == -3 = decodeN 3 0 ns
  | otherwise = n : decode ns

decodeN m z ns
  | m > 0 = decodeN' m z ns
  | otherwise = z : decode ns
decodeN' m z (n:ns) = decodeN (m - 1) (z + n) ns

main = print (decode [1,2,3::Integer])
