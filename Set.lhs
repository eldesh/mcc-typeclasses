% -*- LaTeX -*-
% $Id: Set.lhs 1744 2005-08-23 16:17:12Z wlux $
%
% Copyright (c) 2002, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Set.lhs}
\section{Sets}
The module \texttt{Set} implements sets as a special case of finite
maps.
\begin{verbatim}

> module Set where
> import List
> import Map
> import Maybe

> infixl 8 `addToSet`, `deleteFromSet`
> infixl 7 `unionSet`, `intersectionSet`
> infixl 6 `diffSet`, `symDiffSet`
> infix  4 `subsetSet`, `elemSet`, `notElemSet`

> newtype Set a = Set (FM a ())

\end{verbatim}
Two sets are equal if both contain the same elements.
\begin{verbatim}

> instance Ord a => Eq (Set a) where
>   xs == ys = toListSet xs == toListSet ys

> instance (Ord a, Show a) => Show (Set a) where
>   showsPrec p set =
>     showChar '{' . showElems (map shows (toListSet set)) . showChar '}'
>     where showElems = flip (foldr ($)) . intersperse (showChar ',')      -- $

> nullSet :: Ord a => Set a -> Bool
> nullSet = null . toListSet

> zeroSet :: Ord a => Set a
> zeroSet = Set zeroFM

> unitSet :: Ord a => a -> Set a
> unitSet x = Set (unitFM x ())

> addToSet :: Ord a => a -> Set a -> Set a
> addToSet x (Set xs) = Set (addToFM x () xs)

> deleteFromSet :: Ord a => a -> Set a -> Set a
> deleteFromSet x (Set xs) = Set (deleteFromFM x xs)

> elemSet :: Ord a => a -> Set a -> Bool
> elemSet x (Set xs) = isJust (lookupFM x xs)

> notElemSet :: Ord a => a -> Set a -> Bool
> notElemSet x set = not (elemSet x set)

> subsetSet :: Ord a => Set a -> Set a -> Bool
> subsetSet xs ys = all (`elemSet` ys) (toListSet xs)

> fromListSet :: Ord a => [a] -> Set a
> fromListSet = foldr addToSet zeroSet

> toListSet :: Ord a => Set a -> [a]
> toListSet (Set xs) = map fst (toListFM xs)

> unionSet :: Ord a => Set a -> Set a -> Set a
> unionSet xs ys = foldr addToSet xs (toListSet ys)

> unionSets :: Ord a => [Set a] -> Set a
> unionSets = foldr unionSet zeroSet

> intersectionSet :: Ord a => Set a -> Set a -> Set a
> intersectionSet xs ys =
>   foldr addToSet zeroSet [y | y <- toListSet ys, y `elemSet` xs]

> diffSet :: Ord a => Set a -> Set a -> Set a
> diffSet xs ys = foldr deleteFromSet xs (toListSet ys)

> symDiffSet :: Ord a => Set a -> Set a -> Set a
> symDiffSet xs ys = unionSet (diffSet xs ys) (diffSet ys xs)

> mapSet :: (Ord a, Ord b) => (a -> b) -> Set a -> Set b
> mapSet f = fromListSet . map f . toListSet

> domainFM :: Ord a => FM a b -> Set a
> domainFM = Set . fmap (const ())

\end{verbatim}
