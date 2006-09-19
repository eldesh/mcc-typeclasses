-- $Id: MarshalError.curry 1744 2005-08-23 16:17:12Z wlux $
--
-- Copyright (c) 2005, Wolfgang Lux
-- See ../LICENSE for the full license.

module MarshalError where
import Ptr

throwIf :: (a -> Bool) -> (a -> String) -> IO a -> IO a
throwIf f g m = m >>= \x -> if f x then ioError (g x) else return x

throwIf_ :: (a -> Bool) -> (a -> String) -> IO a -> IO ()
throwIf_ f g m = m >>= \x -> if f x then ioError (g x) else return ()

throwIfNeg :: (Int -> String) -> IO Int -> IO Int
throwIfNeg = throwIf (0 >)

throwIfNeg_ :: (Int -> String) -> IO Int -> IO ()
throwIfNeg_ = throwIf_ (0 >)

throwIfNull :: String -> IO (Ptr a) -> IO (Ptr a)
throwIfNull msg = throwIf (nullPtr ==) (const msg)

void :: IO a -> IO ()
void m = m >> return ()
