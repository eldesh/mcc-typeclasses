-- $Id: StablePtr.curry 1744 2005-08-23 16:17:12Z wlux $
--
-- Copyright (c) 2005, Wolfgang Lux
-- See ../LICENSE for the full license.

module StablePtr where
import Ptr

data StablePtr a

foreign import primitive newStablePtr :: a -> IO (StablePtr a)
foreign import primitive deRefStablePtr :: StablePtr a -> IO a
foreign import primitive freeStablePtr :: StablePtr a -> IO ()

foreign import ccall "prims.h primCastPtr"
        castStablePtrToPtr :: StablePtr a -> Ptr ()
foreign import ccall "prims.h primCastPtr"
        castPtrToStablePtr :: Ptr () -> StablePtr a
