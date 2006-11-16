-- $Id: ForeignPtr.curry 2013 2006-11-16 14:10:51Z wlux $
--
-- Copyright (c) 2005, Wolfgang Lux
-- See ../LICENSE for the full license.

module ForeignPtr where
import Ptr
import MarshalAlloc

type FinalizerPtr a        = FunPtr (           Ptr a -> IO ())
type FinalizerEnvPtr env a = FunPtr (Ptr env -> Ptr a -> IO ())

data ForeignPtr a

instance Eq (ForeignPtr a) where
  p1 == p2 = unsafeForeignPtrToPtr p1 == unsafeForeignPtrToPtr p2
instance Ord (ForeignPtr a) where
  p1 `compare` p2 = unsafeForeignPtrToPtr p1 `compare` unsafeForeignPtrToPtr p2

foreign import primitive "newForeignPtr"
        newForeignPtr_ :: Ptr a -> IO (ForeignPtr a)

newForeignPtr :: FinalizerPtr a -> Ptr a -> IO (ForeignPtr a)
newForeignPtr finalizer ptr =
  do
    fp <- newForeignPtr_ ptr
    addForeignPtrFinalizer finalizer fp
    return fp

newForeignPtrEnv :: FinalizerEnvPtr env a -> Ptr env -> Ptr a
                 -> IO (ForeignPtr a)
newForeignPtrEnv finalizer env ptr =
  do
    fp <- newForeignPtr_ ptr
    addForeignPtrFinalizerEnv finalizer env fp
    return fp

foreign import primitive 
        addForeignPtrFinalizer :: FinalizerPtr a -> ForeignPtr a -> IO ()
foreign import primitive
        addForeignPtrFinalizerEnv :: FinalizerEnvPtr env a -> Ptr env
                                  -> ForeignPtr a -> IO ()

mallocForeignPtrBytes :: Int -> IO (ForeignPtr a)
mallocForeignPtrBytes n = mallocBytes n >>= newForeignPtr finalizerFree

withForeignPtr :: ForeignPtr a -> (Ptr a -> IO b) -> IO b
withForeignPtr fp f =
  do
    x <- f (unsafeForeignPtrToPtr fp)
    touchForeignPtr fp
    return x

foreign import primitive unsafeForeignPtrToPtr :: ForeignPtr a -> Ptr a 
foreign import primitive touchForeignPtr :: ForeignPtr a -> IO ()
foreign import primitive castForeignPtr :: ForeignPtr a -> ForeignPtr b
