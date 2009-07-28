-- $Id: IOExts.curry 2876 2009-07-28 08:46:16Z wlux $
--
-- Copyright (c) 2004-2009, Wolfgang Lux
-- See ../LICENSE for the full license.

module IOExts(fixIO, unsafePerformIO,unsafeInterleaveIO,
 	      IORef, newIORef,readIORef,writeIORef,modifyIORef,
	      IOArray, newIOArray,boundsIOArray,readIOArray,writeIOArray,
	      freezeIOArray,thawIOArray, unsafeFreezeIOArray,unsafeThawIOArray,
 	      hIsTerminalDevice, openFd, openProcess, pClose, connectTcpSocket,
	      trace, performGC) where

import Array
import IO
import IOVector
import Monad
import Unsafe(unsafePerformIO,unsafeInterleaveIO,trace)

-- monadic fix-point operator
foreign import primitive fixIO :: (a -> IO a) -> IO a

-- mutable references
data IORef a
instance Eq (IORef a) where
  (==) = primEqIORef
    where foreign import rawcall "equal.h primEqAddr"
    	  	  	 primEqIORef :: IORef a -> IORef a -> Bool

foreign import primitive newIORef :: a -> IO (IORef a)
foreign import primitive readIORef :: IORef a -> IO a
foreign import primitive writeIORef :: IORef a -> a -> IO ()

modifyIORef :: IORef a -> (a -> a) -> IO ()
modifyIORef r f = readIORef r >>= \x -> writeIORef r (f x)

-- mutable arrays
data Ix a => IOArray a b = IOArray (a,a) (IOVector b)
instance Ix a => Eq (IOArray a b) where
  a1 == a2 =
    case (a1,a2) of
      (IOArray b1 v1,IOArray b2 v2) -> b1 == b2 && v1 == v2

newIOArray :: Ix a => (a,a) -> b -> IO (IOArray a b)
newIOArray b x =
  do
    v <- newIOVector (rangeSize b) x
    return (IOArray b v)

boundsIOArray :: Ix a => IOArray a b -> (a,a)
boundsIOArray (IOArray b _) = b

readIOArray :: Ix a => IOArray a b -> a -> IO b
readIOArray (IOArray b v) i = readIOVector v (index b i)

writeIOArray :: Ix a => IOArray a b -> a -> b -> IO ()
writeIOArray (IOArray b v) i x = writeIOVector v (index b i) x

freezeIOArray :: Ix a => IOArray a b -> IO (Array a b)
freezeIOArray (IOArray b v) =
  do
    v' <- freezeIOVector v
    return (vectorArray b v')

thawIOArray :: Ix a => Array a b -> IO (IOArray a b)
thawIOArray a =
  do
    v <- thawIOVector (vector a)
    return (IOArray (bounds a) v)

unsafeFreezeIOArray :: Ix a => IOArray a b -> IO (Array a b)
unsafeFreezeIOArray (IOArray b v) =
  do
    v' <- unsafeFreezeIOVector v
    return (vectorArray b v')

unsafeThawIOArray :: Ix a => Array a b -> IO (IOArray a b)
unsafeThawIOArray a =
  do
    v <- unsafeThawIOVector (vector a)
    return (IOArray (bounds a) v)

-- assorted IO functions
foreign import rawcall "files.h primHIsTerminalDevice"
	       hIsTerminalDevice :: Handle -> IO Bool

foreign import rawcall "files.h primOpenFd"
	       openFd :: Int -> IOMode -> IO Handle

openProcess :: String -> IOMode -> IO Handle
openProcess cmd mode = (primOpenProcess $## cmd) mode
  where foreign import rawcall "files.h"
  		       primOpenProcess :: String -> IOMode -> IO Handle

foreign import rawcall "files.h primPClose" pClose :: Handle -> IO Int

connectTcpSocket :: String -> Int -> IOMode -> IO Handle
connectTcpSocket host port mode = (primConnectTcpSocket $## host) port mode
  where foreign import rawcall "files.h"
  		       primConnectTcpSocket :: String -> Int -> IOMode -> IO Handle

-- perform a garbage collection
foreign import ccall "primPerformGC" performGC :: IO ()
