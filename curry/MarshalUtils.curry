-- $Id: MarshalUtils.curry 2017 2006-11-21 11:21:49Z wlux $
--
-- Copyright (c) 2005-2006, Wolfgang Lux
-- See ../LICENSE for the full license.

module MarshalUtils where
import Ptr
import Monad

fromBool :: Num a => Bool -> a
fromBool b = if b then 1 else 0

toBool :: Num a => a -> Bool
toBool x = x /= 0

maybeNew :: (a -> IO (Ptr a))
   -> (Maybe a -> IO (Ptr a))
maybeNew f Nothing = return nullPtr
maybeNew f (Just x) = f x

maybeWith :: (a -> (Ptr b -> IO c) -> IO c)
    -> (Maybe a -> (Ptr b -> IO c) -> IO c)
maybeWith f Nothing g = g nullPtr
maybeWith f (Just x) g = f x g

maybePeek :: (Ptr a -> IO b)
          -> (Ptr a -> IO (Maybe b))
maybePeek f p = if p == nullPtr then return Nothing else liftM Just (f p)

foreign import ccall "string.h memcpy"
        copyBytes :: Ptr a -> Ptr a -> Int -> IO ()
foreign import ccall "string.h memmove"
        moveBytes :: Ptr a -> Ptr a -> Int -> IO ()
