-- $Id: MarshalUtils.curry 1744 2005-08-23 16:17:12Z wlux $
--
-- Copyright (c) 2005, Wolfgang Lux
-- See ../LICENSE for the full license.

module MarshalUtils where
import Ptr
import Monad

fromBool :: Bool -> Int
fromBool b = if b then 1 else 0

toBool :: Int -> Bool
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
