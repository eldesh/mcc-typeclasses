-- $Id: Float.curry 2701 2008-05-19 18:26:34Z wlux $
--
-- Copyright (c) 2004-2008, Wolfgang Lux
-- See ../LICENSE for the full license.

module Float((+.), (-.), (*.), (/.), (^.), (^^.), (**.),
             (<.), (>.), (<=.), (>=.),
	     pi, i2f, truncate, round, sqrt, log, log10, exp,
	     sin, cos, tan, asin, acos, atan, atan2, sinh, cosh, tanh) where
infixl 8 ^., ^^., **.

-- (+.), (-.), (*.), (/.) float operators for compatibility with PAKCS
(+.), (-.), (*.), (/.) :: Float -> Float -> Float
(+.) = (+)
(-.) = (-)
(*.) = (*)
(/.) = (/)
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
i2f = fromInt

--- x^.n computes the nth power of x, n must be non-negative
(^.) :: Float -> Int -> Float
(^.) = (^)

--- x^^.n computes the nth power of x, n may be negative
(^^.) :: Float -> Int -> Float
(^^.) = (^^)

--- Power
(**.) :: Float -> Float -> Float
x **. y = exp (log x * y)

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

--- (atan2 y x) computes the principal value of atan (y/x) using the signs of
--- both arguments in order to determine the quadrant the result is in
--- it is useful for converting rectangular coordinates into polar coordinates
foreign import ccall "math.h" atan2 :: Float -> Float -> Float

--- Hyperbolic sine
foreign import ccall "math.h" sinh :: Float -> Float

--- Hyperbolic cosine
foreign import ccall "math.h" cosh :: Float -> Float

--- Hyperbolic tangent
foreign import ccall "math.h" tanh :: Float -> Float
