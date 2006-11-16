-- $Id: IOVector.curry 2011 2006-11-16 12:17:25Z wlux $
--
-- Copyright (c) 2004, Wolfgang Lux
-- See ../LICENSE for the full license.

module IOVector where

-- Primitive vectors

data IOVector a

instance Eq (IOVector a) where
  (==) = primEqIOVector
    where foreign import primitive
                  primEqIOVector :: IOVector a -> IOVector a -> Bool

foreign import primitive newIOVector    :: Int -> a -> IO (IOVector a)
foreign import primitive copyIOVector   :: IOVector a -> IO (IOVector a)
foreign import primitive readIOVector   :: IOVector a -> Int -> IO a
foreign import primitive writeIOVector  :: IOVector a -> Int -> a -> IO ()
foreign import primitive lengthIOVector :: IOVector a -> Int
