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
    where foreign import primitive primEqHandle :: Handle -> Handle -> Bool

data HandlePosn	= HandlePosn Handle Int
instance Eq HandlePosn where
  p1 == p2 =
    case (p1,p2) of
      (HandlePosn h1 n1,HandlePosn h2 n2) -> h1 == h2 && n1 == n2

data IOMode = ReadMode | WriteMode | AppendMode | ReadWriteMode
instance Eq IOMode where
  m1 == m2 =
    case (m1,m2) of
      (ReadMode,ReadMode) -> True
      (WriteMode,WriteMode) -> True
      (AppendMode,AppendMode) -> True
      (ReadWriteMode,ReadWriteMode) -> True
      _ -> False
instance Ord IOMode where
  m1 `compare` m2 =
    case (m1,m2) of
      (ReadMode,ReadMode) -> EQ
      (ReadMode,_)        -> LT
      (WriteMode,ReadMode)  -> GT
      (WriteMode,WriteMode) -> EQ
      (WriteMode,_)         -> LT
      (AppendMode,ReadWriteMode) -> LT
      (AppendMode,AppendMode)    -> EQ
      (AppendMode,_)             -> GT
      (ReadWriteMode,ReadWriteMode) -> EQ
      (ReadWriteMode,_)             -> GT

data BufferMode = NoBuffering | LineBuffering | BlockBuffering (Maybe Int)
instance Eq BufferMode where
  m1 == m2 =
    case (m1,m2) of
      (NoBuffering,NoBuffering) -> True
      (LineBuffering,LineBuffering) -> True
      (BlockBuffering n1,BlockBuffering n2) -> n1 == n2
      _ -> False
instance Ord BufferMode where
  m1 `compare` m2 =
    case (m1,m2) of
      (NoBuffering,NoBuffering) -> EQ
      (NoBuffering,_)           -> LT
      (LineBuffering,NoBuffering)      -> GT
      (LineBuffering,LineBuffering)    -> EQ
      (LineBuffering,BlockBuffering _) -> LT
      (BlockBuffering n1,BlockBuffering n2) -> n1 `compare` n2
      (BlockBuffering _,_)                  -> GT

data SeekMode = AbsoluteSeek | RelativeSeek | SeekFromEnd
instance Eq SeekMode where
  m1 == m2 =
    case (m1,m2) of
      (AbsoluteSeek,AbsoluteSeek) -> True
      (RelativeSeek,RelativeSeek) -> True
      (SeekFromEnd,SeekFromEnd) -> True
      _ -> False
instance Ord SeekMode where
  m1 `compare` m2 =
    case (m1,m2) of
      (AbsoluteSeek,AbsoluteSeek) -> EQ
      (AbsoluteSeek,_)            -> LT
      (RelativeSeek,AbsoluteSeek) -> GT
      (RelativeSeek,RelativeSeek) -> EQ
      (RelativeSeek,SeekFromEnd)  -> LT
      (SeekFromEnd,SeekFromEnd)   -> EQ
      (SeekFromEnd,_)             -> GT

--- Predefined handles for standard input, output, and error
foreign import primitive stdin  :: Handle
foreign import primitive stdout :: Handle
foreign import primitive stderr :: Handle

--- Action to open a file. Returns a handle for the file if successful
--- and raises an IOError otherwise.
foreign import primitive openFile :: FilePath -> IOMode -> IO Handle

--- Action to close a handle. A handle may safely be closed more than once.
foreign import primitive hClose :: Handle -> IO ()

--- Action to check whether a handle is open. A handle is open until closed
--- explicitly with hClose or implicity when hGetContents was applied to
--- it and the file has been read.
foreign import primitive hIsOpen     :: Handle -> IO Bool

--- Action to check whether a handle is closed. A handle is closed
--- explicitly when hClose or hGetContents is applied to it
foreign import primitive hIsClosed   :: Handle -> IO Bool

--- Actions to check whether a handle is readable.
foreign import primitive hIsReadable :: Handle -> IO Bool

--- Action to check whether a handle is writable. 
foreign import primitive hIsWritable :: Handle -> IO Bool

--- Action to check whether a handle is seekable. 
foreign import primitive hIsSeekable :: Handle -> IO Bool

--- Actions that check whether a (readable) handle is at the
--- end-of-file.
foreign import primitive isEOF  :: IO Bool
foreign import primitive hIsEOF :: Handle -> IO Bool

--- Action that returns the size of file.
foreign import primitive hFileSize :: Handle -> IO Int

--- Action to read a single character from an open handle.
foreign import primitive hGetChar :: Handle -> IO Char

--- Action that returns the next character from an open handle
--- but does not remove it from the file buffer
foreign import primitive hLookAhead :: Handle -> IO Char

--- Action to read a single line from an open handle.
foreign import primitive hGetLine :: Handle -> IO String

--- Action that (lazily) reads and closes the handle.
foreign import primitive hGetContents :: Handle -> IO String

--- Action to write a character to an open handle.
foreign import primitive hPutChar :: Handle -> Char -> IO ()

--- Action to write a string to an open handle.
foreign import primitive hPutStr :: Handle -> String -> IO ()

--- Action to write a string with a newline to an open handle.
hPutStrLn :: Handle -> String -> IO ()
hPutStrLn h cs = hPutStr h cs >> hPutChar h '\n'

--- Action that converts a term into a strings and writes it to an open handle.
hPrint :: Handle -> a -> IO ()
hPrint h x = hPutStrLn h (show x)

--- Action to determine the current buffer mode of a handle.
foreign import primitive hGetBuffering :: Handle -> IO BufferMode

--- Action to change the current buffer mode of a handle.
foreign import primitive hSetBuffering :: Handle -> BufferMode -> IO ()

--- Action to flush all buffers associated with the handle.
foreign import primitive hFlush :: Handle -> IO ()

--- Action to save the current I/O position of a handle.
hGetPosn :: Handle -> IO HandlePosn
hGetPosn h =
  do
    p <- hTell h
    return (HandlePosn h p)
  where foreign import primitive hTell :: Handle -> IO Int

--- Action to restore the current I/O position of a handle.
hSetPosn :: HandlePosn -> IO ()
hSetPosn (HandlePosn h p) = hSeek h AbsoluteSeek p

--- Action to change the current I/O position of a handle.
foreign import primitive hSeek :: Handle -> SeekMode -> Int -> IO ()

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
