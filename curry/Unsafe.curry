-- $Id: Unsafe.curry 1819 2005-11-07 15:56:02Z wlux $
--
-- Copyright (c) 2002-2004, Wolfgang Lux
-- See ../LICENSE for the full license.

module Unsafe(unsafePerformIO, unsafeInterleaveIO, trace,
	      spawnConstraint, isVar) where
import IO

foreign import primitive unsafePerformIO :: IO a -> a

unsafeInterleaveIO :: IO a -> IO a
unsafeInterleaveIO m = return (unsafePerformIO m)

trace :: String -> a -> a
trace msg x = unsafePerformIO (hPutStrLn stderr msg) `seq` x

foreign import primitive spawnConstraint :: Success -> a -> a

foreign import primitive isVar :: a -> Bool

