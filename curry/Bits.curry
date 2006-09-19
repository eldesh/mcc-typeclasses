-- $Id: Bits.curry 1744 2005-08-23 16:17:12Z wlux $
--
-- Copyright (c) 2005, Wolfgang Lux
-- See ../LICENSE for the full license.

module Bits((.&.), (.|.), xor, complement, shift, rotate,
            bit, setBit, clearBit, complementBit, testBit,
            bitSize, isSigned, shiftL, shiftR, rotateL, rotateR) where

infixl 8 `shift`, `shiftL`, `shiftR`, `rotate`, `rotateL`, `rotateR`
infixl 7 .&.
infixl 6 `xor`
infixl 5 .|.

foreign import ccall "prims.h primAndInt" (.&.) :: Int -> Int -> Int
foreign import ccall "prims.h primOrInt" (.|.) :: Int -> Int -> Int
foreign import ccall "prims.h primXorInt" xor :: Int -> Int -> Int
foreign import ccall "prims.h primNotInt" complement :: Int -> Int

shift :: Int -> Int -> Int
shift = shiftL

rotate :: Int -> Int -> Int
rotate = rotateL

bit :: Int -> Int
bit n = setBit 0 n

setBit :: Int -> Int -> Int
setBit x n = x .|. shift 1 n

clearBit :: Int -> Int -> Int
clearBit x n = x .&. complement (shift 1 n)

complementBit :: Int -> Int -> Int
complementBit x n = x `xor` shift 1 n

testBit :: Int -> Int -> Bool
testBit x n = x .&. shift 1 n /= 0

bitSize :: Int -> Int
bitSize _ = primBitSizeInt
  where foreign import ccall "prims.h" primBitSizeInt :: Int

isSigned :: Int -> Bool
isSigned _ = True

foreign import ccall "prims.h primShiftLInt" shiftL :: Int -> Int -> Int
foreign import ccall "prims.h primShiftRInt" shiftR :: Int -> Int -> Int

foreign import ccall "prims.h primRotateLInt" rotateL :: Int -> Int -> Int
foreign import ccall "prims.h primRotateRInt" rotateR :: Int -> Int -> Int
