-- $Id: Float.curry 1881 2006-04-03 09:21:01Z wlux $
--
-- Copyright (c) 2004, Wolfgang Lux
-- See ../LICENSE for the full license.

module Float((+.), (-.), (*.), (/.), (^), (^^), (**), (<.), (>.), (<=.), (>=.),
	     pi, i2f, truncate, round, sqrt, log, log10, exp,
	     sin, cos, tan, asin, acos, atan, atan2, sinh, cosh, tanh) where
infixl 8 ^, ^^, **

-- (+.), (-.), (*.), (/.) re-exported from Prelude for compatibility with PAKCS
-- (<.), (>.), (<=.) (>=.) ordering relations of floats
(<.), (>.), (<=.), (>=.) :: Float -> Float -> Bool
(<.) = (<)
(>.) = (>)
(<=.) = (<=)
(>=.) = (>=)

--- Constant pi
pi :: Float
pi = 3.14159265358979323846

--- Convert an integer to a floating point number
i2f :: Int -> Float
i2f = floatFromInt

--- Convert a floating point number to an integer always rounding towards 0
truncate :: Float -> Int
truncate = truncateFloat

--- Convert a floating point number to the nearest integer number
round :: Float -> Int
round = roundFloat

--- x^n computes the nth power of x, n must be non-negative
(^) :: Float -> Int -> Float
x ^ n
  | n > 0 = f x (n - 1) x
  | n == 0 = 1
  where f x n y
          | n == 0 = y
          | otherwise = g x n y
        g x n y =
          if n `rem` 2 == 0 then g (x *. x) (n `quot` 2) y
                            else f x (n - 1) (x *. y)

--- x^^n computes the nth power of x, n may be negative
(^^) :: Float -> Int -> Float
x ^^ n = if n >= 0 then x ^ n else 1 /. x ^ (-n)

--- Power
(**) :: Float -> Float -> Float
x ** y = exp (log x *. y)

--- Square root
foreign import ccall "math.h" sqrt :: Float -> Float

--- Natural logarithm
foreign import ccall "math.h" log :: Float -> Float

--- Logarithm to base 10
foreign import ccall "math.h" log10 :: Float -> Float

--- Natural exponent
foreign import ccall "math.h" exp :: Float -> Float

--- Sine
foreign import ccall "math.h" sin :: Float -> Float

--- Cosine
foreign import ccall "math.h" cos :: Float -> Float

--- Tangent
foreign import ccall "math.h" tan :: Float -> Float

--- Arc sine
foreign import ccall "math.h" asin :: Float -> Float

--- Arc cosine
foreign import ccall "math.h" acos :: Float -> Float

--- Arc tangent
foreign import ccall "math.h" atan :: Float -> Float

--- (atan2 y x) computes the principal value of atan (y/.x) using the signs of
--- both arguments in order to determine the quadrant the result is in
--- it is useful for converting rectangular coordinates into polar coordinates
foreign import ccall "math.h" atan2 :: Float -> Float -> Float

--- Hyperbolic sine
foreign import ccall "math.h" sinh :: Float -> Float

--- Hyperbolic cosine
foreign import ccall "math.h" cosh :: Float -> Float

--- Hyperbolic tangent
foreign import ccall "math.h" tanh :: Float -> Float
