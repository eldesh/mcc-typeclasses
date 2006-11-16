-- $Id: Ptr.curry 2013 2006-11-16 14:10:51Z wlux $
--
-- Copyright (c) 2005, Wolfgang Lux
-- See ../LICENSE for the full license.

module Ptr where

data Ptr a

instance Eq (Ptr a) where
  (==) = primEqPtr
    where foreign import ccall "prims.h" primEqPtr :: Ptr a -> Ptr a -> Bool
instance Ord (Ptr a) where
  p1 `compare` p2 =
    case p1 `primCmpPtr` p2 of
      -1 -> LT
      0  -> EQ
      1  -> GT
    where foreign import ccall "prims.h" primCmpPtr :: Ptr a -> Ptr a -> Int

foreign import ccall "prims.h primNullPtr" nullPtr :: Ptr a
foreign import ccall "prims.h primCastPtr" castPtr :: Ptr a -> Ptr b
foreign import ccall "prims.h primPlusPtr" plusPtr :: Ptr a -> Int -> Ptr b
foreign import ccall "prims.h primAlignPtr" alignPtr :: Ptr a -> Int -> Ptr a
foreign import ccall "prims.h primMinusPtr" minusPtr :: Ptr a -> Ptr b -> Int


data FunPtr a

instance Eq (FunPtr a) where
  (==) = primEqPtr
    where foreign import ccall "prims.h" primEqPtr :: FunPtr a -> FunPtr a -> Bool
instance Ord (FunPtr a) where
  p1 `compare` p2 =
    case p1 `primCmpPtr` p2 of
      -1 -> LT
      0  -> EQ
      1  -> GT
    where foreign import ccall "prims.h" primCmpPtr :: FunPtr a -> FunPtr a -> Int

foreign import ccall "prims.h primNullPtr" nullFunPtr :: FunPtr a
foreign import ccall "prims.h primCastPtr" castFunPtr :: FunPtr a -> FunPtr b
foreign import ccall "prims.h primCastPtr" castFunPtrToPtr :: FunPtr a -> Ptr b
foreign import ccall "prims.h primCastPtr" castPtrToFunPtr :: Ptr a -> FunPtr b
