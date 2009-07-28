-- $Id: AllSolutions.curry 2878 2009-07-28 15:51:55Z wlux $
--
-- Copyright (c) 2004-2009, Wolfgang Lux
-- See ../LICENSE for the full license.

module AllSolutions(SearchTree(..), getSearchTree, allValuesD, allValuesB,
                    getOneSolution, getAllSolutions,
                    getOneValue, getAllValues,
                    getAllFailures) where
import Maybe
import Monad

data SearchTree a = Fail | Val a | Or [SearchTree a] deriving (Eq,Ord,Show)

instance Functor SearchTree where
  fmap _ Fail = Fail
  fmap f (Val x) = Val (f x)
  fmap f (Or ts) = Or (map (fmap f) ts)


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
