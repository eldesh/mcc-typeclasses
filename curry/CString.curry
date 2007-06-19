-- $Id: CString.curry 2296 2007-06-19 22:37:03Z wlux $
--
-- Copyright (c) 2005-2007, Wolfgang Lux
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

newCString :: String -> IO CString
newCString s = newCString $## s
  where foreign import primitive newCString :: String -> IO CString

newCStringLen :: String -> IO CStringLen
newCStringLen s = newCStringLen $## s
  where foreign import primitive newCStringLen :: String -> IO CStringLen

withCString :: String -> (CString -> IO a) -> IO a
withCString cs = bracket (newCString cs) mfree

withCStringLen :: String -> (CStringLen -> IO a) -> IO a
withCStringLen cs = bracket (newCStringLen cs) (mfree . fst)

castCharToCChar :: Char -> CChar
castCharToCChar = id

castCCharToChar :: CChar -> Char
castCCharToChar = id
