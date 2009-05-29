-- $Id: IOVector.curry 2854 2009-05-29 12:33:07Z wlux $
--
-- Copyright (c) 2004-2009, Wolfgang Lux
-- See ../LICENSE for the full license.

module IOVector where

-- Primitive vectors

data Vector a
data IOVector a

instance Eq (IOVector a) where
  (==) = primEqIOVector
    where foreign import rawcall "equal.h primEqAddr"
                  	 primEqIOVector :: IOVector a -> IOVector a -> Bool

foreign import primitive readVector   :: Vector a -> Int -> a
foreign import primitive lengthVector :: Vector a -> Int

foreign import primitive newIOVector    :: Int -> a -> IO (IOVector a)
foreign import primitive readIOVector   :: IOVector a -> Int -> IO a
foreign import primitive writeIOVector  :: IOVector a -> Int -> a -> IO ()
foreign import primitive lengthIOVector :: IOVector a -> Int
foreign import primitive freezeIOVector :: IOVector a -> IO (Vector a)
foreign import primitive thawIOVector   :: Vector a -> IO (IOVector a)

foreign import primitive unsafeFreezeIOVector :: IOVector a -> IO (Vector a)
foreign import primitive unsafeThawIOVector   :: Vector a -> IO (IOVector a)

copyIOVector :: IOVector a -> IO (IOVector a)
copyIOVector v = freezeIOVector v >>= unsafeThawIOVector
