-- This example shows that only some functions in a group of
-- mutually recursive declarations can have ambiguous types.
-- In particular, the types inferred for decode, decodeN, and
-- decodeN' are (Num a1, Ord a1, Num a) => a -> a (decode)
-- and (Num a, Ord a, Num b) => a -> b -> b (decodeN and
-- decodeN'), respectively. Obviously, decode's type is
-- ambiguous, and default resolution should fix the type
-- variable a1 to Integer. However, this also means that the type
-- of decodeN and decodeN' should be (Num a) => Integer -> a -> a.

main = print (decode [1,2,3])
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
