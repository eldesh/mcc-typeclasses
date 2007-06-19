-- $Id: IOExts.curry 2296 2007-06-19 22:37:03Z wlux $
--
-- Copyright (c) 2004-2007, Wolfgang Lux
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

-- used to prevent premature evaluation of foreign function arguments
data Wrap a = Wrap a

-- monadic fix-point operator
foreign import primitive fixIO :: (a -> IO a) -> IO a

-- mutable references
data IORef a
instance Eq (IORef a) where
  (==) = primEqIORef
    where foreign import ccall unsafe "refs.h"
    	  	  	 primEqIORef :: IORef a -> IORef a -> Bool

newIORef :: a -> IO (IORef a)
newIORef x = primNewIORef (Wrap x)
  where foreign import ccall unsafe "refs.h"
  		       primNewIORef :: Wrap a -> IO (IORef a)

foreign import ccall unsafe "refs.h primReadIORef"
	       readIORef :: IORef a -> IO a

writeIORef :: IORef a -> a -> IO ()
writeIORef r x = primWriteIORef r (Wrap x)
  where foreign import ccall unsafe "refs.h"
  		       primWriteIORef :: IORef a -> Wrap a -> IO ()

modifyIORef :: IORef a -> (a -> a) -> IO ()
modifyIORef r f = readIORef r >>= \x -> writeIORef r (f x)

-- mutable arrays
data IOArray a = IOArray (Int,Int) (IOVector a)
instance Eq (IOArray a) where
  a1 == a2 =
    case (a1,a2) of
      (IOArray b1 v1,IOArray b2 v2) -> b1 == b2 && v1 == v2

newIOArray :: (Int,Int) -> a -> IO (IOArray a)
newIOArray b x =
  do
    v <- newIOVector (rangeSize b) x
    return (IOArray b v)

boundsIOArray :: IOArray a -> (Int,Int)
boundsIOArray (IOArray b _) = b

readIOArray :: IOArray a -> Int -> IO a
readIOArray (IOArray b v) i = readIOVector v (index b i)

writeIOArray :: IOArray a -> Int -> a -> IO ()
writeIOArray (IOArray b v) i x = writeIOVector v (index b i) x

freezeIOArray :: IOArray a -> IO (Array a)
freezeIOArray (IOArray b v) = copyIOVector v >>= unsafeArray b

thawIOArray :: Array a -> IO (IOArray a)
thawIOArray a =
  do
    v <- unsafeVector a
    v' <- copyIOVector v
    return (IOArray (bounds a) v')

unsafeFreezeIOArray :: IOArray a -> IO (Array a)
unsafeFreezeIOArray (IOArray b v) = unsafeArray b v

unsafeThawIOArray :: Array a -> IO (IOArray a)
unsafeThawIOArray a =
  do
    v <- unsafeVector a
    return (IOArray (bounds a) v)

-- assorted IO functions
foreign import primitive hIsTerminalDevice :: Handle -> IO Bool
foreign import primitive openFd :: Int -> IOMode -> IO Handle

openProcess :: String -> IOMode -> IO Handle
openProcess cmd mode = (openProcess $## cmd) mode
  where foreign import primitive openProcess :: String -> IOMode -> IO Handle

foreign import primitive pClose :: Handle -> IO Int

connectTcpSocket :: String -> Int -> IOMode -> IO Handle
connectTcpSocket host port mode = (connectTcpSocket $## host) port mode
  where foreign import primitive
  		       connectTcpSocket :: String -> Int -> IOMode -> IO Handle

-- perform a garbage collection
foreign import ccall "primPerformGC" performGC :: IO ()
