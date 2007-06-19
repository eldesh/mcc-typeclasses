-- $Id: CString.curry 2297 2007-06-19 22:51:03Z wlux $
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

peekCString :: CString -> IO String
peekCString p
  | p == nullPtr = ioError "peekCString: nullPtr"
  | otherwise = primPeekCString p
  where foreign import ccall unsafe "cstring.h"
  		       primPeekCString :: Ptr CChar -> IO String

peekCStringLen :: CStringLen -> IO String
peekCStringLen (p,l)
  | l <= 0 = return ""
  | p == nullPtr = ioError "peekCStringLen: nullPtr"
  | otherwise = primPeekCStringLen p l
  where foreign import ccall unsafe "cstring.h"
  		       primPeekCStringLen :: Ptr CChar -> Int -> IO String

newCString :: String -> IO CString
newCString s = primNewCString $## s
  where foreign import ccall unsafe "cstring.h"
  		       primNewCString :: String -> IO CString

newCStringLen :: String -> IO CStringLen
newCStringLen s =  
  do
    p <- newCString s
    return (p,length s)

withCString :: String -> (CString -> IO a) -> IO a
withCString cs = bracket (newCString cs) mfree

withCStringLen :: String -> (CStringLen -> IO a) -> IO a
withCStringLen cs = bracket (newCStringLen cs) (mfree . fst)

castCharToCChar :: Char -> CChar
castCharToCChar = id

castCCharToChar :: CChar -> Char
castCCharToChar = id
