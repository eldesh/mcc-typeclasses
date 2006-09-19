-- $Id: Socket.curry 1903 2006-04-22 18:49:09Z wlux $
--
-- Copyright (c) 2006, Wolfgang Lux
-- See ../LICENSE for the full license.

-- PAKCS compatible socket library for MCC

module Socket(Socket, socketINET, socketBind, socketListen, listenOn,
              socketAccept, waitForSocketAccept, connectToSocket) where
import Ptr
import MarshalAlloc
import MarshalError
import CError
import CString
import IO(Handle, IOMode(..))
import IOExts(openFd)
import Unsafe(isVar)

-- (Abstract) Socket type
newtype Socket = Socket Int


-- Creates a new INET socket. Use socketBind, socketListen, and
-- socketAccept for establishing a server for this socket.
socketINET :: IO Socket
socketINET =
  do
    s <- throwErrnoIfMinus1 "socketINET" (socket AF_INET SOCK_STREAM 0)
    return (Socket s)

foreign import ccall "Socket.h prim_AF_INET" AF_INET :: Int
foreign import ccall "Socket.h prim_SOCK_STREAM" SOCK_STREAM :: Int
foreign import ccall "Socket.h socket" socket :: Int -> Int -> Int -> IO Int


-- Binds a socket to a port number. If the port number is a free
-- variable, the system picks a port number and binds the variable
-- to it.
socketBind :: Socket -> Int -> IO ()
socketBind (Socket s) port
  | Unsafe.isVar port =
      do
        throwErrnoIfMinus1_ "socketBind" (prim_bind s 0)
        port' <- throwErrnoIfMinus1 "getsockname" (prim_getPort s)
        doSolve (port =:= port')
  | otherwise = throwErrnoIfMinus1_ "socketBind" (prim_bind s port)

foreign import ccall "Socket.h" prim_bind :: Int -> Int -> IO Int
foreign import ccall "Socket.h" prim_getPort :: Int -> IO Int


-- Defines the maximum backlog queue of a port.
socketListen :: Socket -> Int -> IO ()
socketListen (Socket s) backlog =
  throwErrnoIfMinus1_ "socketListen" (listen s backlog)

foreign import ccall "Socket.h" listen :: Int -> Int -> IO Int


-- Creates a server side socket bound to a port number. If the port
-- number is a free variable, the system picks a port number and binds
-- the variable to it. The implementation currently uses a queue limit
-- of 10 connections.
listenOn :: Int -> IO Socket
listenOn port =
  do
    s <- socketINET
    socketBind s port
    socketListen s 10
    return s


-- Returns a connection of a client to a socket. The connection is
-- returned as a pair consisting of a string identifying the client
-- (the format of this string is implementation-dependent) and a handle
-- to a stream communication with the client. The handle is both readable
-- and writable.
socketAccept :: Socket -> IO (String,Handle)
socketAccept (Socket s) =
  do
    fd <- throwErrnoIfMinus1 "accept" (accept s nullPtr nullPtr)
    host <- throwErrnoIfNull "getpeername" (prim_getPeer fd) >>= peekCString
    hdl <- openFd fd ReadWriteMode
    return (host,hdl)

data SockAddr
foreign import ccall "Socket.h"
	accept :: Int -> Ptr SockAddr -> Ptr Int -> IO Int
foreign import ccall "Socket.h"
	prim_getPeer :: Int -> IO CString


-- Waits until a connection of a client to a socket is available. If
-- no connection is available within the time limit, it returns Nothing,
-- otherwise the connection is returned as a pair consisting of a string
-- identifying the client (the format of this string is
-- implementation-dependent) and a handle to a stream communication with
-- the client.
--
-- Example call: (waitForSocketAccept socket timeout)
-- Parameters:
--   socket - a socket
--   timeout - milliseconds to wait for input (< 0 : no time out)
waitForSocketAccept :: Socket -> Int -> IO (Maybe (String,Handle))
waitForSocketAccept (Socket s) timeout
  | timeout >= 0 =
      do
        n <- prim_waitForInput s timeout
        case n of
          -1 -> throwErrno "socket"
          0 -> return Nothing
          _ -> socketAccept (Socket s) >>= \r -> return (Just r)
  | otherwise = socketAccept (Socket s) >>= \r -> return (Just r)

foreign import ccall "Socket.h" prim_waitForInput :: Int -> Int -> IO Int


-- Creates a new connection to a Unix socket.
-- Example call: (connectToSocket host port)
-- Parameters:
--   host - the host name of the connection
--   port - the port number of the connection
-- Returns:
--   the handle of the stream (connected to the port port@host)
--   which is both readable and writable
connectToSocket :: String -> Int -> IO Handle
connectToSocket host port =
  do
    h <- throwIfNull ("unknown host: " ++ host) (withCString host gethostbyname)
    Socket s <- socketINET
    throwErrnoIfMinus1_ "connectToSocket" (prim_connect s h port)
    openFd s ReadWriteMode

data HostEnt
foreign import ccall "Socket.h"
	gethostbyname :: CString -> IO (Ptr HostEnt)
foreign import ccall "Socket.h"
	prim_connect :: Int -> Ptr HostEnt -> Int -> IO Int
