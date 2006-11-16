-- $Id: Ptr.curry 2011 2006-11-16 12:17:25Z wlux $
--
-- Copyright (c) 2005, Wolfgang Lux
-- See ../LICENSE for the full license.

module Ptr where

data Ptr a

instance Eq (Ptr a) where
  (==) = primEqPtr
    where foreign import ccall "prims.h" primEqPtr :: Ptr a -> Ptr a -> Bool

foreign import ccall "prims.h primNullPtr" nullPtr :: Ptr a
foreign import ccall "prims.h primCastPtr" castPtr :: Ptr a -> Ptr b
foreign import ccall "prims.h primPlusPtr" plusPtr :: Ptr a -> Int -> Ptr b
foreign import ccall "prims.h primAlignPtr" alignPtr :: Ptr a -> Int -> Ptr a
foreign import ccall "prims.h primMinusPtr" minusPtr :: Ptr a -> Ptr b -> Int


data FunPtr a

instance Eq (FunPtr a) where
  (==) = primEqPtr
    where foreign import ccall "prims.h" primEqPtr :: FunPtr a -> FunPtr a -> Bool

foreign import ccall "prims.h primNullPtr" nullFunPtr :: FunPtr a
foreign import ccall "prims.h primCastPtr" castFunPtr :: FunPtr a -> FunPtr b
foreign import ccall "prims.h primCastPtr" castFunPtrToPtr :: FunPtr a -> Ptr b
foreign import ccall "prims.h primCastPtr" castPtrToFunPtr :: Ptr a -> FunPtr b
