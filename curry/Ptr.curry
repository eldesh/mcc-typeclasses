-- $Id: Ptr.curry 2024 2006-11-27 23:33:32Z wlux $
--
-- Copyright (c) 2005, Wolfgang Lux
-- See ../LICENSE for the full license.

module Ptr where

data Ptr a

instance Eq (Ptr a) where
  (==) = primEqPtr
    where foreign import ccall "prims.h" primEqPtr :: Ptr a -> Ptr a -> Bool
  (/=) = primNeqPtr
    where foreign import ccall "prims.h" primNeqPtr :: Ptr a -> Ptr a -> Bool
instance Ord (Ptr a) where
  (<) = primLtPtr
    where foreign import ccall "prims.h" primLtPtr :: Ptr a -> Ptr a -> Bool
  (<=) = primLeqPtr
    where foreign import ccall "prims.h" primLeqPtr :: Ptr a -> Ptr a -> Bool
  (>=) = primGeqPtr
    where foreign import ccall "prims.h" primGeqPtr :: Ptr a -> Ptr a -> Bool
  (>) = primGtPtr
    where foreign import ccall "prims.h" primGtPtr :: Ptr a -> Ptr a -> Bool

foreign import ccall "prims.h primNullPtr" nullPtr :: Ptr a
foreign import ccall "prims.h primCastPtr" castPtr :: Ptr a -> Ptr b
foreign import ccall "prims.h primPlusPtr" plusPtr :: Ptr a -> Int -> Ptr b
foreign import ccall "prims.h primAlignPtr" alignPtr :: Ptr a -> Int -> Ptr a
foreign import ccall "prims.h primMinusPtr" minusPtr :: Ptr a -> Ptr b -> Int


data FunPtr a

instance Eq (FunPtr a) where
  (==) = primEqPtr
    where foreign import ccall "prims.h" primEqPtr :: FunPtr a -> FunPtr a -> Bool
  (/=) = primNeqPtr
    where foreign import ccall "prims.h" primNeqPtr :: FunPtr a -> FunPtr a -> Bool
instance Ord (FunPtr a) where
  (<) = primLtPtr
    where foreign import ccall "prims.h" primLtPtr :: FunPtr a -> FunPtr a -> Bool
  (<=) = primLeqPtr
    where foreign import ccall "prims.h" primLeqPtr :: FunPtr a -> FunPtr a -> Bool
  (>=) = primGeqPtr
    where foreign import ccall "prims.h" primGeqPtr :: FunPtr a -> FunPtr a -> Bool
  (>) = primGtPtr
    where foreign import ccall "prims.h" primGtPtr :: FunPtr a -> FunPtr a -> Bool

foreign import ccall "prims.h primNullPtr" nullFunPtr :: FunPtr a
foreign import ccall "prims.h primCastPtr" castFunPtr :: FunPtr a -> FunPtr b
foreign import ccall "prims.h primCastPtr" castFunPtrToPtr :: FunPtr a -> Ptr b
foreign import ccall "prims.h primCastPtr" castPtrToFunPtr :: Ptr a -> FunPtr b
