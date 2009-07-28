-- $Id: Float.curry 2874 2009-07-28 07:39:39Z wlux $
--
-- Copyright (c) 2004-2009, Wolfgang Lux
-- See ../LICENSE for the full license.

-- NB This module is obsolete and exists only to provide compatibility
--    with PAKCS

module Float((+.), (-.), (*.), (/.), (^.), (^^.), (**.),
             (<.), (>.), (<=.), (>=.),
	     pi, i2f, truncate, round, sqrt, log, log10, exp,
	     sin, cos, tan, asin, acos, atan, atan2, sinh, cosh, tanh) where
infixl 8 ^., ^^., **.

-- (+.), (-.), (*.), (/.) float operators for compatibility with PAKCS
(+.), (-.), (*.), (/.) :: Floating a => a -> a -> a
(+.) = (+)
(-.) = (-)
(*.) = (*)
(/.) = (/)
-- (<.), (>.), (<=.) (>=.) ordering relations of floats
(<.), (>.), (<=.), (>=.) :: RealFloat a => a -> a -> Bool
(<.) = (<)
(>.) = (>)
(<=.) = (<=)
(>=.) = (>=)

--- Convert an integer to a floating point number
i2f :: Floating a => Int -> a
i2f = fromInt

--- x^.n computes the nth power of x, n must be non-negative
(^.) :: Floating a => a -> Int -> a
(^.) = (^)

--- x^^.n computes the nth power of x, n may be negative
(^^.) :: Floating a => a -> Int -> a
(^^.) = (^^)

--- Power
(**.) :: Floating a => a -> a -> a
(**.) = (**)

--- Logarithm to base 10
log10 :: Floating a => a -> a
log10 x = logBase 10 x
