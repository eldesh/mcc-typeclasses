-- $Id: System.curry 3094 2012-08-13 09:52:16Z wlux $
--
-- Copyright (c) 2002-2012, Wolfgang Lux
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

curryExitWith :: Int -> IO a
curryExitWith rc = exit_with rc >> undefined
  where foreign import ccall exit_with :: Int -> IO ()
        -- NB exit_with does not return and therefore should have type
        --    Int -> IO a, but this type is not a valid foreign type for
        --    the ccall calling convention.

exitWith :: ExitCode -> IO a
exitWith ExitSuccess = curryExitWith 0
exitWith (ExitFailure n) = curryExitWith (if n == 0 then 1 else n)

exitFailure :: IO a
exitFailure = exitWith (ExitFailure 1)
