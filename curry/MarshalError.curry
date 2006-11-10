-- $Id: MarshalError.curry 1996 2006-11-10 20:05:36Z wlux $
--
-- Copyright (c) 2005-2006, Wolfgang Lux
-- See ../LICENSE for the full license.

module MarshalError where
import Ptr

throwIf :: (a -> Bool) -> (a -> String) -> IO a -> IO a
throwIf f g m = m >>= \x -> if f x then ioError (g x) else return x

throwIf_ :: (a -> Bool) -> (a -> String) -> IO a -> IO ()
throwIf_ f g m = m >>= \x -> if f x then ioError (g x) else return ()

throwIfNeg :: Num a => (a -> String) -> IO a -> IO a
throwIfNeg = throwIf (fromInt 0 >)

throwIfNeg_ :: Num a => (a -> String) -> IO a -> IO ()
throwIfNeg_ = throwIf_ (fromInt 0 >)

throwIfNull :: String -> IO (Ptr a) -> IO (Ptr a)
throwIfNull msg = throwIf (nullPtr ==) (const msg)

void :: IO a -> IO ()
void m = m >> return ()
