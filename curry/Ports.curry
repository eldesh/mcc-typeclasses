-- $Id: Ports.curry 3273 2016-07-13 21:23:01Z wlux $
--
-- Copyright (c) 2004-2016, Wolfgang Lux
-- See ../LICENSE for the full license.

-- Ports implementation for MCC

module Ports(Port, SP_Msg(..),
             openPort, closePort, send, doSend, choiceSPEP,
             openProcessPort, openSocketConnectPort, newObject) where

import IO
import IOExts
import Unsafe


-- Local ports

newtype Port a = Port (IORef [a]) deriving Eq

openPort :: Port a -> [a] -> Bool
openPort (Port r) ms = r =:= unsafePerformIO (newIORef ms)

closePort :: Port a -> Bool
closePort (Port r) = unsafePerformIO (readIORef r) =:= []

-- NB: the message must be evaluated to normal form *before* the
--     port is updated; hence the guard expression.
send :: a -> Port a -> Bool
send m (Port r) | m =:= m' =
  unsafePerformIO (do ms <- readIORef r; writeIORef r ms'; return ms) =:= m':ms'
  where m',ms' free

doSend :: a -> Port a -> IO ()
doSend m p = doSolve (send m p)


-- Stream ports

data SP_Msg = SP_Put String
            | SP_GetLine String
            | SP_GetChar Char
            | SP_EOF Bool
            | SP_Close
            deriving (Eq,Ord,Show)

openProcessPort :: String -> IO (Port SP_Msg)
openProcessPort cmd =
  openProcess cmd ReadWriteMode >>= streamPort closeProcess
  where closeProcess h = pClose h >> return ()

openSocketConnectPort :: Int -> String -> IO (Port SP_Msg)
openSocketConnectPort port host =
  connectTcpSocket host port ReadWriteMode >>= streamPort hClose

streamPort :: (Handle -> IO ()) -> Handle -> IO (Port SP_Msg)
streamPort hClose h =
  do
    hSetBuffering h LineBuffering
    doSolve (openPort p ms)
    spawnConstraint (unsafePerformIO (backgroundTask ms)) (return p)
  where backgroundTask ms =
	  do
	     mapIO_ (msg . ensureNotFree) (ensureSpine ms)
	     hClose h
	     return True
	msg (SP_Put s) = hPutStrLn h s
	msg (SP_GetLine s) = hGetLine h >>= doSolve . (s =:=)
	msg (SP_GetChar c) = hGetChar h >>= doSolve . (c =:=)
	msg (SP_EOF b) = hIsEOF h >>= doSolve . (b =:=)
	msg SP_Close = hClose h
        p,ms free


-- Merging

{- NB The function choiceSPEP should use a fair choice. However, since
      committed choice is currently not supported, the unsafe primitive
      isVar is used as a (poor) workaround. -}
choiceSPEP :: Port SP_Msg -> [a] -> Either String [a]
choiceSPEP sp ep
  | isVar ep = chooseSP sp
  | otherwise =
      case ep of
        ms@(_:_) -> Right ms
        _ -> chooseSP sp
  where chooseSP sp | send (SP_GetLine s) sp = Left s where s free


-- Active objects

newObject :: (a -> [b] -> Bool) -> a -> Port b -> Bool
newObject f s p = openPort p ms & f s (map ensureNotFree (ensureSpine ms))
  where ms free
