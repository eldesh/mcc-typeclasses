-- This example shows that only some functions in a group of
-- mutually recursive declarations can have ambiguous types.
-- In particular, the types inferred for decode, decodeN, and
-- decodeN' are (Bounded a1, Enum a1, Ord a1, Num a) => a -> a
-- (decode) and (Bounded  a, Enum a, Ord a, Num b) => a -> b -> b
-- (decodeN and decodeN'), respectively. Obviously, decode's type
-- is ambiguous and since it does involve Num or one its subclasses
-- every use of this function remains ambiguous.

main = print (decode [1,2,3])
  where decode [] = []
        decode (n:ns)
          | n == -1 = decodeN (succ minBound) 0 ns
          | n == -2 = decodeN (succ (succ minBound)) 0 ns
          | n == -3 = decodeN (succ (succ (succ minBound))) 0 ns
          | otherwise = n : decode ns

        decodeN m z ns
          | m > minBound = decodeN' m z ns
          | otherwise = z : decode ns
        decodeN' m z (n:ns) = decodeN (pred m) (z + n) ns
