-- $Id: MarshalAlloc.curry 1744 2005-08-23 16:17:12Z wlux $
--
-- Copyright (c) 2005, Wolfgang Lux
-- See ../LICENSE for the full license.

module MarshalAlloc where
import Ptr
import IO

foreign import ccall "stdlib.h malloc"
        mallocBytes :: Int -> IO (Ptr a)

allocaBytes :: Int -> (Ptr a -> IO b) -> IO b
allocaBytes n = bracket (mallocBytes n) mfree

foreign import ccall "stdlib.h realloc"
        reallocBytes :: Ptr a -> Int -> IO (Ptr b)

foreign import ccall "stdlib.h free"
        mfree :: Ptr a -> IO ()

-- NB The type of finalizerFree is FinalizerPtr a in the FFI addendum.
-- However, we cannot import that type here because of a cyclic import
-- dependency.
foreign import ccall "stdlib.h &free" finalizerFree :: FunPtr (Ptr a -> IO ())
