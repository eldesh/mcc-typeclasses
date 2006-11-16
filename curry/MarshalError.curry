-- $Id: MarshalError.curry 2013 2006-11-16 14:10:51Z wlux $
--
-- Copyright (c) 2005-2006, Wolfgang Lux
-- See ../LICENSE for the full license.

module MarshalError where
import Ptr

throwIf :: (a -> Bool) -> (a -> String) -> IO a -> IO a
throwIf f g m = m >>= \x -> if f x then ioError (g x) else return x

throwIf_ :: (a -> Bool) -> (a -> String) -> IO a -> IO ()
throwIf_ f g m = m >>= \x -> if f x then ioError (g x) else return ()

throwIfNeg :: (Ord a,Num a) => (a -> String) -> IO a -> IO a
throwIfNeg = throwIf (0 >)

throwIfNeg_ :: (Ord a,Num a) => (a -> String) -> IO a -> IO ()
throwIfNeg_ = throwIf_ (0 >)

throwIfNull :: String -> IO (Ptr a) -> IO (Ptr a)
throwIfNull msg = throwIf (nullPtr ==) (const msg)

void :: IO a -> IO ()
void m = m >> return ()
