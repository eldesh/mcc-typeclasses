-- Here is another test mixing literal and constructor patterns in the
-- same expression. The essential point here is that the constructor
-- patterns must not hide the numeric literals and vice versa.

data Nat = Z | S Nat deriving (Eq,Show)

instance Num Nat where
  fromInteger n
    | n > 0 = S (fromInteger (n - 1))
    | n == 0 = Z
  Z + n = n
  S m + S n = S (m + n)
  m   - Z = m
  S m - S n = m - n
  -- other methods omitted

f xy =
  case xy of
    (0,Nothing) -> 'a'
    (Z,Just False) -> 'b'
    (0,Just True) -> 'c'
    (1,Nothing) -> 'd'
    (S _,Nothing) -> 'e'
    (1,Just False) -> 'f'
    (S _,Just False) -> 'g'
    (1,Just True) -> 'h'
    (S _,Just True) -> 'i'

main = print (map f [(x,y) | x <- [0,1,2], y <- [Nothing,Just False,Just True]])
