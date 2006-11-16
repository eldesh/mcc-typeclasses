-- sets based on finite maps

-- Copyright (c) 2002-2006, Wolfgang Lux
-- See ../LICENSE for the full license.

module Set(Set, showSet,showsSet,
           nullSet, zeroSet, unitSet, addToSet, deleteFromSet,
	   elemSet, notElemSet, subsetSet, fromListSet, toListSet,
	   unionSet, unionSets, intersectionSet, diffSet, symDiffSet,
	   mapSet, domainFM) where
import Maybe
import FiniteMap

infixl 8 `addToSet`, `deleteFromSet`
infixl 7 `unionSet`, `intersectionSet`
infixl 6 `diffSet`, `symDiffSet`
infix  4 `subsetSet`, `elemSet`, `notElemSet`

newtype Set a = Set (FM a ())

instance Eq a => Eq (Set a) where
  xs == ys = toListSet xs == toListSet ys

showSet :: Set a -> String
showSet set = showsSet set ""

showsSet :: Set a -> ShowS
showsSet set =
  case toListSet set of
    [] -> showString "{}"
    (x:xs) -> showChar '{' . shows x . showl xs
      where showl [] = showChar '}'
            showl (x:xs) = showChar ',' . shows x . showl xs

nullSet :: Set a -> Bool
nullSet xs = null (toListSet xs)

zeroSet :: Set a
zeroSet = Set zeroFM

unitSet :: a -> Set a
unitSet x = Set (unitFM x ())

addToSet :: a -> Set a -> Set a
addToSet x (Set xs) = Set (addToFM x () xs)

deleteFromSet :: a -> Set a -> Set a
deleteFromSet x (Set xs) = Set (deleteFromFM x xs)

elemSet :: a -> Set a -> Bool
elemSet x (Set xs) = isJust (lookupFM x xs)

notElemSet :: a -> Set a -> Bool
notElemSet x set = not (elemSet x set)

subsetSet :: Set a -> Set a -> Bool
subsetSet xs ys = all (`elemSet` ys) (toListSet xs)

fromListSet :: [a] -> Set a
fromListSet = foldr addToSet zeroSet

toListSet :: Set a -> [a]
toListSet (Set xs) = map fst (toListFM xs)

unionSet :: Set a -> Set a -> Set a
unionSet xs ys = foldr addToSet xs (toListSet ys)

unionSets :: [Set a] -> Set a
unionSets = foldr unionSet zeroSet

intersectionSet :: Set a -> Set a -> Set a
intersectionSet xs ys =
  foldr addToSet zeroSet [y | y <- toListSet ys, y `elemSet` xs]

diffSet :: Set a -> Set a -> Set a
diffSet xs ys = foldr deleteFromSet xs (toListSet ys)

symDiffSet :: Set a -> Set a -> Set a
symDiffSet xs ys = unionSet (diffSet xs ys) (diffSet ys xs)

mapSet :: (a -> b) -> Set a -> Set b
mapSet f xs = fromListSet (map f (toListSet xs))

domainFM :: FM a b -> Set a
domainFM xs = Set (mapFM (const ()) xs)
