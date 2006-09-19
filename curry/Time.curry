-- $Id: Time.curry 1744 2005-08-23 16:17:12Z wlux $
--
-- Copyright (c) 2003-2005, Wolfgang Lux
-- See ../LICENSE for the full license.

module Time(ClockTime, getClockTime) where
import Ptr
import CTypes
import CError

type ClockTime = CTime
type CTime = CLong

getClockTime :: IO ClockTime
getClockTime = throwErrnoIfMinus1 "getClockTime" (time nullPtr)
  where foreign import ccall "time.h" time :: Ptr CTime -> IO CTime
