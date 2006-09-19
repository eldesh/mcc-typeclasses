-- $Id: Random.curry 1744 2005-08-23 16:17:12Z wlux $
--
-- Copyright (c) 2004, Wolfgang Lux
-- See ../LICENSE for the full license.

module Random where

data StdGen

foreign import primitive genRange	   :: StdGen -> (Int,Int)
foreign import primitive "nextStdGen" next :: StdGen -> (Int,StdGen)
foreign import primitive mkStdGen	   :: Int -> StdGen

split :: StdGen -> (StdGen,StdGen)
split rng = (mkStdGen x,mkStdGen y)
  where (x,rng') = next rng
  	(y,_) = next rng'

random :: StdGen -> (Int,StdGen)
random = next

randomR :: (Int,Int) -> StdGen -> (Int,StdGen)
randomR (lo,hi) = nextRStdGen lo hi
  where foreign import primitive nextRStdGen :: Int -> Int -> StdGen -> (Int,StdGen)

randoms :: StdGen -> [Int]
randoms rng = x : randoms rng'
  where (x,rng') = random rng

randomRs :: (Int,Int) -> StdGen -> [Int]
randomRs range rng = x : randomRs range rng'
  where (x,rng') = randomR range rng

randomIO :: IO Int
randomIO = getStdRandom random

randomRIO :: (Int,Int) -> IO Int
randomRIO range = getStdRandom (randomR range)

foreign import primitive getStdGen :: IO StdGen
foreign import primitive setStdGen :: StdGen -> IO ()

newStdGen :: IO StdGen
newStdGen =
  do
    rng <- getStdGen
    let (rng1,rng2) = split rng
    setStdGen rng1
    return rng2

getStdRandom :: (StdGen -> (a,StdGen)) -> IO a
getStdRandom random =
  do
    rng <- getStdGen
    let (x,rng') = random rng
    setStdGen rng'
    return x
