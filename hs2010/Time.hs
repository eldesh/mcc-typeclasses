module Time(ClockTime,Month(..),Day(..),CalendarTime(..),TimeDiff(..),
            getClockTime,addToClockTime,diffClockTimes,
            toCalendarTime,toUTCTime,toClockTime,
            calendarTimeToString,formatCalendarTime) where
import System.Time
