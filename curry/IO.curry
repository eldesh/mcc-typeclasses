-- $Id: IO.curry 2853 2009-05-29 11:55:01Z wlux $
--
-- Copyright (c) 2003-2007, Wolfgang Lux
-- See ../LICENSE for the full license.

module IO(Handle, HandlePosn, IOMode(..), BufferMode(..), SeekMode(..),
          stdin, stdout, stderr,
	  openFile, hClose, 
	  hIsOpen, hIsClosed, hIsReadable, hIsWritable, hIsSeekable,
	  isEOF, hIsEOF, hFileSize, 
	  hGetChar, hLookAhead, hGetLine, hGetContents,
	  hPutChar, hPutStr, hPutStrLn, hPrint,
	  hGetBuffering, hSetBuffering, hFlush,
	  hGetPosn, hSetPosn, hSeek,
	  tryIO, bracket, bracket_,
          {- re-exported Prelude entities -}
	  IO, FilePath, IOError, ioError, catch, interact,
	  putChar, putStr, putStrLn, print, getChar, getLine, getContents,
	  readFile, writeFile, appendFile) where

data Handle
instance Eq Handle where
  (==) = primEqHandle
    where foreign import rawcall "equal.h primEqAddr"
    	  	  	 primEqHandle :: Handle -> Handle -> Bool
instance Show Handle where
  -- FIXME: use a dedicated primitive for this
  showsPrec _ = shows where foreign import primitive shows :: a -> ShowS

data HandlePosn	= HandlePosn Handle Int deriving (Eq,Show)

data IOMode =
  ReadMode | WriteMode | AppendMode | ReadWriteMode
  deriving (Eq,Ord,Bounded,Enum,Show)

data BufferMode =
  NoBuffering | LineBuffering | BlockBuffering (Maybe Int)
  deriving (Eq,Ord,Show)

data SeekMode =
  AbsoluteSeek | RelativeSeek | SeekFromEnd
  deriving (Eq,Ord,Bounded,Enum,Show)

--- Predefined handles for standard input, output, and error
foreign import rawcall "files.h primStdin"  stdin  :: Handle
foreign import rawcall "files.h primStdout" stdout :: Handle
foreign import rawcall "files.h primStderr" stderr :: Handle

--- Action to open a file. Returns a handle for the file if successful
--- and raises an IOError otherwise.
openFile :: FilePath -> IOMode -> IO Handle
openFile fn mode = (primOpenFile $## fn) mode
  where foreign import rawcall "files.h"
  		       primOpenFile :: FilePath -> IOMode -> IO Handle

--- Action to close a handle. A handle may safely be closed more than once.
foreign import rawcall "files.h primHClose" hClose :: Handle -> IO ()

--- Action to check whether a handle is open. A handle is open until closed
--- explicitly with hClose or implicity when hGetContents was applied to
--- it and the file has been read.
foreign import rawcall "files.h primHIsOpen" hIsOpen :: Handle -> IO Bool

--- Action to check whether a handle is closed. A handle is closed
--- explicitly when hClose or hGetContents is applied to it
foreign import rawcall "files.h primHIsClosed" hIsClosed :: Handle -> IO Bool

--- Actions to check whether a handle is readable.
foreign import rawcall "files.h primHIsReadable"
	       hIsReadable :: Handle -> IO Bool

--- Action to check whether a handle is writable. 
foreign import rawcall "files.h primHIsWritable"
	       hIsWritable :: Handle -> IO Bool

--- Action to check whether a handle is seekable. 
foreign import rawcall "files.h primHIsSeekable"
	       hIsSeekable :: Handle -> IO Bool

--- Actions that check whether a (readable) handle is at the
--- end-of-file.
foreign import rawcall "files.h primHIsEOF" hIsEOF :: Handle -> IO Bool

isEOF :: IO Bool
isEOF = hIsEOF stdin

--- Action that returns the size of file.
foreign import rawcall "files.h primHFileSize" hFileSize :: Handle -> IO Int

--- Action to read a single character from an open handle.
foreign import rawcall "files.h primHGetChar" hGetChar :: Handle -> IO Char

--- Action that returns the next character from an open handle
--- but does not remove it from the file buffer
foreign import rawcall "files.h primHLookAhead" hLookAhead :: Handle -> IO Char

--- Action to read a single line from an open handle.
foreign import rawcall "files.h primHGetLine" hGetLine :: Handle -> IO String

--- Action that (lazily) reads and closes the handle.
foreign import rawcall "files.h primHGetContents"
	       hGetContents :: Handle -> IO String

--- Action to write a character to an open handle.
foreign import rawcall "files.h primHPutChar"
	       hPutChar :: Handle -> Char -> IO ()

--- Action to write a string to an open handle.
hPutStr :: Handle -> String -> IO ()
hPutStr h = mapIO_ (hPutChar h)

--- Action to write a string with a newline to an open handle.
hPutStrLn :: Handle -> String -> IO ()
hPutStrLn h cs = hPutStr h cs >> hPutChar h '\n'

--- Action that converts a term into a strings and writes it to an open handle.
hPrint :: Show a => Handle -> a -> IO ()
hPrint h x = hPutStrLn h (show x)

--- Action to determine the current buffer mode of a handle.
foreign import rawcall "files.h primHGetBuffering"
	       hGetBuffering :: Handle -> IO BufferMode

--- Action to change the current buffer mode of a handle.
hSetBuffering :: Handle -> BufferMode -> IO ()
hSetBuffering h b = primHSetBuffering h $## b
  where foreign import rawcall "files.h"
		       primHSetBuffering :: Handle -> BufferMode -> IO ()

--- Action to flush all buffers associated with the handle.
foreign import rawcall "files.h primHFlush" hFlush :: Handle -> IO ()

--- Action to save the current I/O position of a handle.
hGetPosn :: Handle -> IO HandlePosn
hGetPosn h =
  do
    p <- primHTell h
    return (HandlePosn h p)
  where foreign import rawcall "files.h" primHTell :: Handle -> IO Int

--- Action to restore the current I/O position of a handle.
hSetPosn :: HandlePosn -> IO ()
hSetPosn (HandlePosn h p) = hSeek h AbsoluteSeek p

--- Action to change the current I/O position of a handle.
foreign import rawcall "files.h primHSeek"
	       hSeek :: Handle -> SeekMode -> Int -> IO ()

--- tryIO executes an IO action and either returns the exception value
--- or the result of the action.
tryIO :: IO a -> IO (Either IOError a)
tryIO m = catch (m >>= return . Right) (return . Left)

--- execute IO actions before and after an IO action
--- <CODE>bracket before after m</CODE> executes the actions in the
--- order before, m, and after. The IO action after is executed even
--- if an exception occurs in m. The result of before is passed to
--- m and after.
bracket :: IO a -> (a -> IO b) -> (a -> IO c) -> IO c
bracket before after m =
  do
    x <- before
    r <- catch (m x) (\ioe -> after x >> ioError ioe)
    after x
    return r

--- execute IO actions before and after an IO action
--- <CODE>bracket before after m</CODE> executes the actions in the
--- order before, m, and after. The IO action after is executed even
--- if an exception occurs in m. The result of before is passed to after.
bracket_ :: IO a -> (a -> IO b) -> IO c -> IO c
bracket_ before after m =
  do
    x <- before
    r <- catch m (\ioe -> after x >> ioError ioe)
    after x
    return r
