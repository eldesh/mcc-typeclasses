-- $Id: Random.curry 2280 2007-06-19 11:40:35Z wlux $
--
-- Copyright (c) 2004-2006, Wolfgang Lux
-- See ../LICENSE for the full license.

module Random where

data StdGen
instance Show StdGen where
  -- FIXME: use a dedicated primitive for this
  showsPrec _ = shows where foreign import primitive shows :: a -> ShowS

foreign import primitive mkStdGen :: Int -> StdGen

next :: StdGen -> (Int,StdGen)
next rng = randomR (genRange rng) rng

genRange :: StdGen -> (Int,Int)
genRange _ = (minBound,maxBound)

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
