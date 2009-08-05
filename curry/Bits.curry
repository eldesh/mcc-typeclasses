-- $Id: Bits.curry 2880 2009-08-05 14:34:49Z wlux $
--
-- Copyright (c) 2005-2009, Wolfgang Lux
-- See ../LICENSE for the full license.

module Bits(Bits(..)) where

infixl 8 `shift`, `shiftL`, `shiftR`, `rotate`, `rotateL`, `rotateR`
infixl 7 .&.
infixl 6 `xor`
infixl 5 .|.

class Num a => Bits a where
  (.&.), (.|.), xor :: a -> a -> a
  complement :: a -> a
  shift, rotate :: a -> Int -> a
  bit :: Int -> a
  setBit, clearBit, complementBit :: a -> Int -> a
  testBit :: a -> Int -> Bool
  bitSize :: a -> Int
  isSigned :: a -> Bool
  shiftL, shiftR :: a -> Int -> a
  rotateL, rotateR :: a -> Int -> a

  -- Minimal complete definition:
  -- (.&.), (.|.), xor, complement, shift, rotate, bitSize, isSigned
  bit n = setBit 0 n
  setBit x n = x .|. shift 1 n
  clearBit x n = x .&. complement (shift 1 n)
  complementBit x n = x `xor` shift 1 n
  testBit x n = x .&. shift 1 n /= 0
  shiftL n = shift n
  shiftR n = shift (-n)
  rotateL n = rotate n
  rotateR n = rotate (-n)

instance Bits Int where
  (.&.) = primAndInt
    where foreign import ccall "prims.h" primAndInt :: Int -> Int -> Int
  (.|.) = primOrInt
    where foreign import ccall "prims.h" primOrInt :: Int -> Int -> Int
  xor = primXorInt
    where foreign import ccall "prims.h" primXorInt :: Int -> Int -> Int
  complement = primNotInt
    where foreign import ccall "prims.h" primNotInt :: Int -> Int
  shift = shiftL
  rotate = rotateL
  bitSize _ = primBitSizeInt
    where foreign import ccall "prims.h" primBitSizeInt :: Int
  isSigned _ = True
  shiftL = primShiftLInt
    where foreign import ccall "prims.h" primShiftLInt :: Int -> Int -> Int
  shiftR = primShiftRInt
    where foreign import ccall "prims.h" primShiftRInt :: Int -> Int -> Int
  rotateL = primRotateLInt
    where foreign import ccall "prims.h" primRotateLInt :: Int -> Int -> Int
  rotateR = primRotateRInt
    where foreign import ccall "prims.h" primRotateRInt :: Int -> Int -> Int

instance Bits Integer where
  (.&.) = primAndInteger
    where foreign import rawcall "integer.h"
    	  	  primAndInteger :: Integer -> Integer -> Integer
  (.|.) = primOrInteger
    where foreign import rawcall "integer.h"
    	  	  primOrInteger :: Integer -> Integer -> Integer
  xor = primXorInteger
    where foreign import rawcall "integer.h"
    	  	  primXorInteger :: Integer -> Integer -> Integer
  complement = primNotInteger
    where foreign import rawcall "integer.h"
    	  	  primNotInteger :: Integer -> Integer
  setBit = primSetBitInteger
    where foreign import rawcall "integer.h"
    	  	  primSetBitInteger :: Integer -> Int -> Integer
  clearBit = primClearBitInteger
    where foreign import rawcall "integer.h"
    	  	  primClearBitInteger :: Integer -> Int -> Integer
  complementBit = primComplBitInteger
    where foreign import rawcall "integer.h"
    	  	  primComplBitInteger :: Integer -> Int -> Integer
  testBit = primTestBitInteger
    where foreign import rawcall "integer.h"
    	  	  primTestBitInteger :: Integer -> Int -> Bool
  shift = primShiftInteger
    where foreign import rawcall "integer.h"
    	  	  primShiftInteger :: Integer -> Int -> Integer
  rotate = shift
  bitSize _ = error "bitSize(Integer)"
  isSigned _ = True
