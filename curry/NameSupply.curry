-- $Id: NameSupply.curry 1882 2006-04-03 11:04:54Z wlux $
--
-- Copyright (c) 2006, Wolfgang Lux
-- See ../LICENSE for the full license.

-- Implementation of unique name supplies based on
-- Lennart Augustsson, Mikael Rittri, Dan Synek. On generating
-- unique names. In: Journal of Functional Programming 4(1), 1994,
-- pp. 117--123.

module NameSupply(NameSupply, initialNameSupply,
                  splitNameSupply, listNameSupply,
                  Name, getName, listName) where

import IOExts

data NameSupply = Splittable Name NameSupply NameSupply
type Name = Int

initialNameSupply :: IO NameSupply
initialNameSupply =
  do
    r <- newIORef 0
    let getName r =
          do
            n <- readIORef r
            writeIORef r (n + 1)
            return n
        mk_supply :: IORef Name -> NameSupply
        mk_supply r =
          Splittable (unsafePerformIO (getName r)) (mk_supply r) (mk_supply r)
    return (mk_supply r)

splitNameSupply :: NameSupply -> (NameSupply,NameSupply)
splitNameSupply (Splittable n s1 s2) = (s1,s2)

getName :: NameSupply -> Name
getName (Splittable n s1 s2) = n

listNameSupply :: NameSupply -> [NameSupply]
listNameSupply s = s1 : listNameSupply s2
  where (s1,s2) = splitNameSupply s

listName :: NameSupply -> [Name]
listName s = getName s : listName (snd (splitNameSupply s))
