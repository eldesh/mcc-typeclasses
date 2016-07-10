-- This program demonstrates an issue with phantom types and type
-- contexts. Depending on when type synonmys are expanded, the types of
-- T1 and T2 are either equivalent, or T1 will have type
--   Eq a => Int -> T1 a
-- and a type signature will be necessary in order to disambiguate all
-- uses of T1.

type Phantom a b = b
data Eq a => T1 a = T1 (Phantom a Int) deriving Show
data Eq a => T2 a = T2 Int             deriving Show

-- either sum1 :: [T1 a] -> T1 b
-- or     sum1 :: (Eq a, Eq b) -> [T1 a] -> T1 b
sum1 = T1 . foldr (\(T1 x) -> (x +)) 0

-- sum2 :: [T2 a] -> T2 b
sum2 = T2 . foldr (\(T2 x) -> (x +)) 0


main =
  -- Depending on when type synonyms are expanded, it may be possible
  -- to omit the expression type signatures below
  print (sum1 ([T1 0, T1 1, T1 2] :: [T1 Bool]) :: T1 ()) >>
  print (sum2 [T2 0, T2 1, T2 2])
