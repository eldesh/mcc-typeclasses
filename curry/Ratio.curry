module Ratio(Ratio, Rational, (%), numerator, denominator, approxRational) where

infixl 7 %

data Integral a => Ratio a = a :% a deriving (Eq)
                                        -- FIXME: use strict fields
type Rational = Ratio Integer

(%) :: Integral a => a -> a -> Ratio a
x % y = reduce (x * signum y) (abs y)

reduce x y
  | y == 0 = error "Ratio.% : zero denominator"
  | otherwise = (x `quot` d) :% (y `quot` d)
  where d = gcd x y

numerator, denominator :: Integral a => Ratio a -> a
numerator (x :% _) = x
denominator (_ :% y) = y

approxRational :: RealFrac a => a -> a -> Rational
approxRational x eps = simplest (x - eps) (x + eps)
  where simplest x y
          | y < x = simplest y x
          | x == y = xr
          | x > 0 = simplest' n d n' d'
          | y < 0 = - simplest' (-n') d' (-n) d
          | otherwise = 0 :% 1
          where xr@(n :% d) = toRational x
                (n' :% d') = toRational y
        simplest' n d n' d'         -- assumes 0 < n%d < n'%d'
          | r == 0 = q :% 1
          | q /= q' = (q+1) :% 1
          | otherwise = (q * n'' + d'') :% n''
          where (q,r) = quotRem n d
                (q',r') = quotRem n' d'
                (n'' :% d'') = simplest' d' r' d r

instance Integral a => Ord (Ratio a) where
  (x1 :% y1) < (x2 :% y2) = x1 * y2 < x2 * y1
  (x1 :% y1) <= (x2 :% y2) = x1 * y2 <= x2 * y1
  (x1 :% y1) >= (x2 :% y2) = x1 * y2 >= x2 * y1
  (x1 :% y1) > (x2 :% y2) = x1 * y2 > x2 * y1
  (x1 :% y1) `compare` (x2 :% y2) = (x1 * y2) `compare` (x2 * y1)

instance Integral a => Num (Ratio a) where
  (x1 :% y1) + (x2 :% y2) = reduce (x1 * y2 + x2 * y1) (y1 * y2)
  (x1 :% y1) - (x2 :% y2) = reduce (x1 * y2 - x2 * y1) (y1 * y2)
  (x1 :% y1) * (x2 :% y2) = reduce (x1 * x2) (y1 * y2)
  negate (x :% y) = (-x) :% y
  abs (x :% y) = abs x :% y
  signum (x :% _) = signum x :% 1
  fromInt x = fromInt x :% 1
  fromInteger x = fromInteger x :% 1

instance Integral a => Real (Ratio a) where
  toRational (x :% y) = toInteger x :% toInteger y

instance Integral a => Fractional (Ratio a) where
  (x1 :% y1) / (x2 :% y2) = (x1 * y2) % (y1 * x2)
  recip (x :% y) = y :% x
  fromRational (x :% y) = fromInteger x :% fromInteger y

instance Integral a => RealFrac (Ratio a) where
  properFraction (x :% y) = (fromIntegral q, r :% y)
    where (q,r) = quotRem x y

instance Integral a => Enum (Ratio a) where
  succ x = x + (1:%1)
  pred x = x - (1:%1)
  toEnum = fromIntegral
  fromEnum = fromInteger . truncate -- May overflow
  enumFrom n = iterate (1 +) n
  enumFromThen n1 n2 = iterate ((n2 - n1) +) n1
  enumFromTo n m = takeWhile (m + 1/2 >=) (enumFrom n)
  enumFromThenTo n1 n2 m = takeWhile p (enumFromThen n1 n2)
    where p = if n2 >= n1 then (m + (n2-n1)/2 >=) else (m + (n2-n1)/2 <=)

instance Integral a => Show (Ratio a) where
  showsPrec p (x :% y) =
    showParen (p > 7) (showsPrec 8 x . showString " % " . showsPrec 8 y)

{- FIXME: include the following definition in the Prelude -}
gcd x y | x /= 0 && y /= 0 = gcd' (abs x) (abs y)
  where gcd' x y = if y == 0 then x else gcd' y (x `rem` y)
