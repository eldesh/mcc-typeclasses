-- This empty module is present only for backward compatibility with hbc,
-- which required the Haskell'98 Time module to provide the Ord instance
-- of the ClockTime type, which was the result type of the
-- Directory.getModificationTime IO action.

-- The Time and Directory modules were dropped from the Haskell 2010
-- standard, but still present as System.Time and System.Directory in
-- ghc 7. The System.Time module was removed without a direct replacement
-- in ghc 8 and the result type of System.Directory.getModificationTime
-- changed to Data.Time.Clock.UTCTime.

module Time({-ClockTime,Month(..),Day(..),CalendarTime(..),TimeDiff(..),
            getClockTime,addToClockTime,diffClockTimes,
            toCalendarTime,toUTCTime,toClockTime,
            calendarTimeToString,formatCalendarTime-}) where
--import System.Time
