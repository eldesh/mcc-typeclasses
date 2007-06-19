-- $Id: StablePtr.curry 2291 2007-06-19 21:54:15Z wlux $
--
-- Copyright (c) 2005-2007, Wolfgang Lux
-- See ../LICENSE for the full license.

module StablePtr(StablePtr, newStablePtr, deRefStablePtr, freeStablePtr,
       	         castStablePtrToPtr, castPtrToStablePtr) where
import Ptr

data StablePtr a

-- Workaround to prevent premature evaluation of the argument of
-- newStablePtr. This cannot be a newtype!
data Wrap a = Wrap a

newStablePtr :: a -> IO (StablePtr a)
newStablePtr x = primNewStablePtr (Wrap x)
  where foreign import ccall unsafe "stable.h"
  		       primNewStablePtr :: Wrap a -> IO (StablePtr a)
foreign import ccall unsafe "stable.h primDeRefStablePtr"
	       deRefStablePtr :: StablePtr a -> IO a
foreign import ccall "stable.h primFreeStablePtr"
	       freeStablePtr :: StablePtr a -> IO ()

foreign import ccall "prims.h primCastPtr"
        castStablePtrToPtr :: StablePtr a -> Ptr ()
foreign import ccall "prims.h primCastPtr"
        castPtrToStablePtr :: Ptr () -> StablePtr a
