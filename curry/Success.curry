-- $Id: Success.curry 3273 2016-07-13 21:23:01Z wlux $
--
-- Copyright (c) 2002-2016, Wolfgang Lux
-- See ../LICENSE for the full license.

module Success(module Success, Success, success, (&), (&>), ground) where
infix  0 ==>, <==

{- Redefinition of Prelude entity for backward compatibility -}
ground = ensureGround

-- Computes the concurrent conjunction of a list of constraints
andC :: [Bool] -> Bool
andC = foldr (&) True

-- Computes the sequential conjunction of a list of constraints
andS :: [Bool] -> Bool
andS = foldr (&>) True

-- Is a given predicate satisfied by all elements in a list?
allC :: (a -> Bool) -> [a] -> Bool
allC p = andC . map p

-- (c ==> x) evaluates x if the constraint c is satisfied
(==>) :: Bool -> a -> a
c ==> x | c = x

-- (x <== c) is equivalent to (c ==> x)
(<==) :: a -> Bool -> a
x <== c | c = x

-- (choose xs) non-deterministically chooses one element from the list xs
choose (x:xs) = choosep x xs
  where choosep x [] = x
        choosep x (_:_) = x
        choosep _ (x:xs) = choosep x xs
