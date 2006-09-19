-- $Id: IOVector.curry 1744 2005-08-23 16:17:12Z wlux $
--
-- Copyright (c) 2004, Wolfgang Lux
-- See ../LICENSE for the full license.

module IOVector where

-- Primitive vectors

data IOVector a

foreign import primitive newIOVector    :: Int -> a -> IO (IOVector a)
foreign import primitive copyIOVector   :: IOVector a -> IO (IOVector a)
foreign import primitive readIOVector   :: IOVector a -> Int -> IO a
foreign import primitive writeIOVector  :: IOVector a -> Int -> a -> IO ()
foreign import primitive lengthIOVector :: IOVector a -> Int
