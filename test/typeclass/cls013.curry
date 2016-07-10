-- Test for the evaluation of non-deterministic methods with missing
-- arguments. The goals g1 and g2 both should have only two solutions,
-- namely [S (S Z), S (S Z)] and [Z, Z]
data Nat = Z | S Nat | P Nat deriving (Eq,Show)

toNat :: Int -> Nat
toNat n
  | n > 0 = S (toNat (n - 1))
  | n == 0 = Z
  | otherwise  = negNat (toNat (- n))

fromNat :: Nat -> Int
fromNat (S x) = fromNat x + 1
fromNat Z     = 0
fromNat (P x) = fromNat x - 1


addNat Z     y = y
addNat (S x) y = succNat (addNat x y)
addNat (P x) y = predNat (addNat x y)

subNat Z     y = negNat y
subNat (S x) y = succNat (subNat x y)
subNat (P x) y = predNat (subNat x y)

negNat Z = Z
negNat (S x) = P (negNat x)
negNat (P x) = S (negNat x)

succNat Z     = S Z
succNat (S x) = S (S x)
succNat (P x) = x

predNat Z     = P Z
predNat (S x) = x
predNat (P x) = P (P x)

instance Num Nat where
  (+) = addNat ? subNat
  (-) = subNat ? addNat
  negate = negNat
  fromInt = toNat

f1 = addNat ? subNat
f2 = subNat ? addNat

l = [S Z,S Z]
g1 = zipWith (+) l l
g2 = zipWith f1 l l

main = g1
