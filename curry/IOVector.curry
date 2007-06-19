-- $Id: IOVector.curry 2294 2007-06-19 22:08:56Z wlux $
--
-- Copyright (c) 2004-2007, Wolfgang Lux
-- See ../LICENSE for the full license.

module IOVector(IOVector, newIOVector, copyIOVector, readIOVector,
		writeIOVector, lengthIOVector) where

-- used to prevent premature evaluation of foreign function arguments
data Wrap a = Wrap a

-- Primitive vectors

data IOVector a

instance Eq (IOVector a) where
  (==) = primEqIOVector
    where foreign import ccall unsafe "vector.h"
                  	 primEqIOVector :: IOVector a -> IOVector a -> Bool

newIOVector    :: Int -> a -> IO (IOVector a)
newIOVector n x = primNewIOVector n (Wrap x)
  where foreign import ccall unsafe "vector.h"
  		       primNewIOVector :: Int -> Wrap a -> IO (IOVector a)

foreign import ccall unsafe "vector.h primCopyIOVector"
	       copyIOVector :: IOVector a -> IO (IOVector a)

foreign import ccall unsafe "vector.h primReadIOVector"
	       readIOVector :: IOVector a -> Int -> IO a

writeIOVector  :: IOVector a -> Int -> a -> IO ()
writeIOVector v i x = primWriteIOVector v i (Wrap x)
  where foreign import ccall unsafe "vector.h"
  		       primWriteIOVector :: IOVector a -> Int -> Wrap a -> IO ()

foreign import ccall unsafe "vector.h primLengthIOVector"
	       lengthIOVector :: IOVector a -> Int
