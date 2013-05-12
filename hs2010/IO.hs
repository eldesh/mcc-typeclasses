module IO(Handle,HandlePosn,IOMode(..),BufferMode(..),SeekMode(..),
          stdin,stdout,stderr, 
          openFile,hClose,hFileSize,hIsEOF,isEOF,
          hSetBuffering,hGetBuffering,hFlush, 
          hGetPosn,hSetPosn,hSeek, 
          hWaitForInput,hReady,hGetChar,hGetLine,hLookAhead,hGetContents, 
          hPutChar,hPutStr,hPutStrLn,hPrint,
          hIsOpen,hIsClosed,hIsReadable,hIsWritable,hIsSeekable,
          isAlreadyExistsError,isDoesNotExistError,isAlreadyInUseError, 
          isFullError,isEOFError,isIllegalOperation,isPermissionError,
          isUserError, 
          ioeGetErrorString,ioeGetHandle,ioeGetFileName,
          IO.try,IO.bracket,IO.bracket_,
          -- ...and what the Prelude exports
          IO,FilePath,IOError,ioError,userError,IO.catch,interact,
          putChar,putStr,putStrLn,print,getChar,getLine,getContents,
          readFile,writeFile,appendFile,readIO,readLn) where
import System.IO
import System.IO.Error
-- NB The next import is not part of Haskell 2010, but it is present on
-- all compilers where this code is used (currently ghc>=7.2). So it is
-- safe to cheat.
import Control.Exception

try :: IO a -> IO (Either IOError a)
try = Control.Exception.try

catch :: IO a -> (IOError -> IO a) -> IO a
catch = Control.Exception.catch

bracket :: IO a -> (a -> IO b) -> (a -> IO c) -> IO c
bracket before after m =
  do
    x  <- before
    rs <- IO.try (m x)
    after x
    case rs of
      Right r -> return r
      Left  e -> ioError e

bracket_ :: IO a -> (a -> IO b) -> IO c -> IO c
bracket_ before after m =
  do
    x  <- before
    rs <- IO.try m
    after x
    case rs of
      Right r -> return r
      Left  e -> ioError e
