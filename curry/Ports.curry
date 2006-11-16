-- $Id: Ports.curry 2013 2006-11-16 14:10:51Z wlux $
--
-- Copyright (c) 2004-2006, Wolfgang Lux
-- See ../LICENSE for the full license.

-- Ports implementation for MCC

module Ports(Port, SP_Msg(..),
             openPort, closePort, send, doSend, choiceSPEP,
             openProcessPort, openSocketConnectPort, newObject) where

import IO
import IOExts
import Unsafe


-- Local ports

newtype Port a = Port (IORef [a])

instance Eq (Port a) where
  Port p1 == Port p2 = p1 == p2


openPort :: Port a -> [a] -> Success
openPort (Port r) ms = r =:= unsafePerformIO (newIORef ms)

closePort :: Port a -> Success
closePort (Port r) = unsafePerformIO (readIORef r) =:= []

-- NB: the message must be evaluated to normal form *before* the
--     port is updated; hence the guard expression.
send :: a -> Port a -> Success
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

instance Eq SP_Msg where
  m1 == m2 =
    case (m1,m2) of
      (SP_Put s1,SP_Put s2) -> s1 == s2
      (SP_GetLine s1,SP_GetLine s2) -> s1 == s2
      (SP_GetChar c1,SP_GetChar c2) -> c1 == c2
      (SP_EOF b1,SP_EOF b2) -> b1 == b2
      (SP_Close,SP_Close) -> True
instance Ord SP_Msg where
  m1 `compare` m2 =
    case (m1,m2) of
      (SP_Put s1,SP_Put s2) -> s1  `compare` s2
      (SP_Put _,_)          -> LT
      (SP_GetLine _,SP_Put _)       -> GT
      (SP_GetLine s1,SP_GetLine s2) -> s1 `compare` s2
      (SP_GetLine _,_)              -> LT
      (SP_GetChar _,SP_Put _)       -> GT
      (SP_GetChar _,SP_GetLine _)   -> GT
      (SP_GetChar c1,SP_GetChar c2) -> c1 `compare` c2
      (SP_GetChar _,_)              -> LT
      (SP_EOF _,SP_Close)   -> LT
      (SP_EOF b1,SP_EOF b2) -> b1 `compare` b2
      (SP_EOF _,_)          -> GT
      (SP_Close,SP_Close) -> EQ
      (SP_Close,_)        -> GT

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
	     return success
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

newObject :: (a -> [b] -> Success) -> a -> Port b -> Success
newObject f s p = openPort p ms & f s (map ensureNotFree (ensureSpine ms))
  where ms free
