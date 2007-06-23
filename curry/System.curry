-- $Id: System.curry 2352 2007-06-23 11:09:53Z wlux $
--
-- Copyright (c) 2002-2005, Wolfgang Lux
-- See ../LICENSE for the full license.

module System(ExitCode(..),
              getArgs, getProgName, getEnv,
	      system, exitWith, exitFailure) where
import Ptr
import CTypes
import CString
import CError
import MarshalError

data ExitCode = ExitSuccess | ExitFailure Int deriving (Eq,Ord,Show)

foreign import ccall curry_argc :: IO Int
foreign import ccall curry_argv :: IO (Ptr CString)

getArgs :: IO [String]
getArgs =
  do
    n <- curry_argc
    p <- curry_argv
    mapIO (\p -> peekPtr p >>= peekCString)
          (tail' (take n (iterate (`plusPtr` sizeOfPtr) p)))
  where tail' [] = []
  	tail' (_:xs) = xs

getProgName :: IO String
getProgName =
  do
    throwIf_ (<= 0) (const "getProgName: illegal operation") curry_argc
    curry_argv >>= peekPtr >>= peekCString

getEnv :: String -> IO String
getEnv var = throwIfNull msg (withCString var getenv) >>= peekCString
  where msg = var ++ ": environment variable does not exist"
        foreign import ccall "stdlib.h" getenv :: CString -> IO CString

system :: String -> IO ExitCode
system cmd = withCString cmd primSystem >>= return . exitCode
  where exitCode r = if r == 0 then ExitSuccess else ExitFailure r
        foreign import ccall "files.h" primSystem :: CString -> IO Int

curryExit :: Int -> IO a
curryExit rc = curry_exit rc >> undefined
  where foreign import ccall curry_exit :: Int -> IO ()
        -- NB curry_exit does not return and therefore should have
        --    type Int -> IO a, but this type is not a valid foreign
        --    type for the ccall calling convention.

exitWith :: ExitCode -> IO a
exitWith ExitSuccess = curryExit 0 >> undefined
exitWith (ExitFailure n) = curryExit (if n == 0 then 1 else n) >> undefined

exitFailure :: IO a
exitFailure = exitWith (ExitFailure 1)
