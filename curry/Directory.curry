module Directory({-Permissions(..),-}
                 createDirectory, removeDirectory, removeFile,
		 renameDirectory, renameFile, getDirectoryContents,
		 getCurrentDirectory, setCurrentDirectory,
		 doesFileExist, doesDirectoryExist,
		 {-getPermissions, setPermissions,-}
		 getModificationTime) where

import IO
import Monad
import Time
import Ptr
import MarshalAlloc
import MarshalUtils
import CString
import CError

-- data Permissions = Permissions {
--   readable, writable, executable, searchable :: Bool
-- }


{- Creating and removing directories and files -}
-- NB unlink is used instead of remove because the latter does
--    also remove directories
foreign import ccall "directory.h" mkdir :: CString -> Int -> IO Int
foreign import ccall "directory.h" rmdir :: CString -> IO Int
foreign import ccall "directory.h" unlink :: CString -> IO Int

createDirectory :: FilePath -> IO ()
createDirectory path =
  throwErrnoIfMinus1_ "createDirectory" (withCString path (flip mkdir 0o777))

removeDirectory :: FilePath -> IO ()
removeDirectory path =
  throwErrnoIfMinus1_ "removeDirectory" (withCString path rmdir)

removeFile :: FilePath -> IO ()
removeFile path = throwErrnoIfMinus1_ "removeFile" (withCString path unlink)


{- Renaming directories and files -}
foreign import ccall "directory.h" rename_d :: CString -> CString -> IO Int
foreign import ccall "directory.h" rename_f :: CString -> CString -> IO Int

renameDirectory :: FilePath -> FilePath -> IO ()
renameDirectory from to =
  throwErrnoIfMinus1_ "renameDirectory"
                      (withCString from (withCString to . rename_d))

renameFile :: FilePath -> FilePath -> IO ()
renameFile from to =
  throwErrnoIfMinus1_ "renameFile"
                      (withCString from (withCString to . rename_f))


{- Directory contents -}
data DIR
data DirEnt

foreign import ccall "directory.h" opendir :: CString -> IO (Ptr DIR)
foreign import ccall "directory.h" closedir :: Ptr DIR -> IO Int
foreign import ccall "directory.h" readdir :: Ptr DIR -> IO (Ptr DirEnt)
foreign import ccall "directory.h" dirent_d_name :: Ptr DirEnt -> CString

getDirectoryContents :: FilePath -> IO [FilePath]
getDirectoryContents path = bracket (openDirectory path) closedir readEntries

openDirectory :: FilePath -> IO (Ptr DIR)
openDirectory path =
  throwErrnoIfNull "getDirectoryContents" (withCString path opendir)

readEntries :: Ptr DIR -> IO [FilePath]
readEntries dir =
  readdir dir >>= \dp ->
  if dp == nullPtr then
    return []
  else
    peekCString (dirent_d_name dp) >>= \file ->
    liftM (file :) (readEntries dir)


{- Managing the current directory -}
foreign import ccall "directory.h" getcwd :: CString -> Int -> IO CString
foreign import ccall "directory.h" chdir :: CString -> IO Int
foreign import ccall "directory.h" maxpathlen :: Int

getCurrentDirectory :: IO FilePath
getCurrentDirectory =
  let n = maxpathlen in
  throwErrnoIfNull "getCurrentDirectory" (allocaBytes n (flip getcwd n)) >>=
  peekCString

setCurrentDirectory :: FilePath -> IO ()
setCurrentDirectory path =
  throwErrnoIfMinus1_ "setCurrentDirectory" (withCString path chdir)


{- Managing file attributes -}
foreign import ccall "directory.h" exist_f :: CString -> IO Int
foreign import ccall "directory.h" exist_d :: CString -> IO Int
foreign import ccall "directory.h" modtime :: CString -> IO ClockTime

doesFileExist :: FilePath -> IO Bool
doesFileExist path =
  liftM toBool (throwErrnoIfMinus1 "doesFileExist" (withCString path exist_f))

doesDirectoryExist :: FilePath -> IO Bool
doesDirectoryExist path =
  liftM toBool
        (throwErrnoIfMinus1 "doesDirectoryExist" (withCString path exist_d))

-- getPermissions :: FilePath -> IO Permissions
-- setPermissions :: FilePath -> Permissions -> IO ()

getModificationTime :: FilePath -> IO ClockTime
getModificationTime path =
  throwErrnoIfMinus1 "getModificationTime" (withCString path modtime)
