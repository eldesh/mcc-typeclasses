-- $Id: CString.curry 1744 2005-08-23 16:17:12Z wlux $
--
-- Copyright (c) 2005, Wolfgang Lux
-- See ../LICENSE for the full license.

module CString where
import Ptr
import CTypes
import MarshalAlloc
import IO

type CString    = Ptr CChar
type CStringLen = (Ptr CChar, Int)

foreign import primitive peekCString :: CString -> IO String
foreign import primitive peekCStringLen :: CStringLen -> IO String

foreign import primitive newCString :: String -> IO CString
foreign import primitive newCStringLen :: String -> IO CStringLen

withCString :: String -> (CString -> IO a) -> IO a
withCString cs = bracket (newCString cs) mfree

withCStringLen :: String -> (CStringLen -> IO a) -> IO a
withCStringLen cs = bracket (newCStringLen cs) (mfree . fst)

castCharToCChar :: Char -> CChar
castCharToCChar = id

castCCharToChar :: CChar -> Char
castCCharToChar = id
