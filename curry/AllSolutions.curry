-- $Id: AllSolutions.curry 1878 2006-04-03 09:06:10Z wlux $
--
-- Copyright (c) 2004, Wolfgang Lux
-- See ../LICENSE for the full license.

module AllSolutions(SearchTree(..), getSearchTree, allValuesD, allValuesB,
                    getOneSolution, getAllSolutions,
                    getOneValue, getAllValues,
                    getAllFailures) where
import Maybe
import Monad

data SearchTree a = Fail | Val a | Or [SearchTree a]

foreign import primitive encapsulate :: a -> IO (a -> Success)

getSearchTree :: a -> IO (SearchTree a)
getSearchTree x = encapsulate x >>= \g -> return (tree g)
  where tree g =
          case try g of
            [] -> Fail
            [g] -> Val (unpack g)
            gs -> Or (map tree gs)

allValuesD :: SearchTree a -> [a]
allValuesD Fail    = []
allValuesD (Val v) = [v]
allValuesD (Or ts) = concatMap allValuesD ts

allValuesB :: SearchTree a -> [a]
allValuesB t = all [t]
  where all ts
          | null ts = []
          | otherwise = [x | Val x <- ts] ++ all [t | Or ts' <- ts, t <- ts']

getOneSolution :: (a -> Success) -> IO (Maybe a)
getOneSolution g = liftM listToMaybe (getAllSolutions g)

getAllSolutions :: (a -> Success) -> IO [a]
getAllSolutions g = getAllValues (unpack g)

getOneValue :: a -> IO (Maybe a)
getOneValue x = liftM listToMaybe (getAllValues x)

getAllValues :: a -> IO [a]
getAllValues x = liftM allValuesD (getSearchTree x)

getAllFailures :: a -> (a -> Success) -> IO [a]
getAllFailures x g = getAllValues x >>= filterM (liftM null . getAllValues . g)
