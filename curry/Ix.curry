module Ix where

range :: (Int,Int) -> [Int]
range (m,n) = [m .. n]

index :: (Int,Int) -> Int -> Int
index r@(m,_) i
  | inRange r i = i - m

inRange :: (Int,Int) -> Int -> Bool
inRange (m,n) i = m <= i && i <= n

rangeSize :: (Int,Int) -> Int
rangeSize (m,n)
  | m <= n    = n - m + 1
  | otherwise = 0
