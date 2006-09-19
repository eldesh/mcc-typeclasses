module List(module List,
	    {- entities re-exported from Prelude-}
	    map, (++), concat, filter,
	    head, {-last,-} tail, {-init,-} null, length, (!!),
	    foldl, foldl1, {-scanl, scanl1,-} foldr, foldr1, {-scanr, scanr1,-}
	    iterate, repeat, replicate, {-cycle,-}
	    take, drop, splitAt, takeWhile, dropWhile, span, break,
	    lines, words, unlines, unwords, reverse, and, or,
	    any, all, elem, notElem, lookup,
	    {-sum, product, maximum, minimum,-} concatMap,
	    zip, zip3, zipWith, zipWith3, unzip, unzip3) where

import Maybe(listToMaybe)

infix 5 \\

{- functions not yet defined in Prelude: -}

init :: [a] -> [a]
init (x:xs) = initp x xs
  where initp _  []      = []
  	initp x1 (x2:xs) = x1 : initp x2 xs

last :: [a] -> a
last (x:xs) = lastp x xs
  where lastp x []     = x
  	lastp _ (x:xs) = lastp x xs

scanl :: (a -> b -> a) -> a -> [b] -> [a]
scanl f z xs = z : scanRest f z xs
  where scanRest f z [] = []
	scanRest f z (x:xs) = scanl f (f z x) xs

scanl1 :: (a -> a -> a) -> [a] -> [a]
scanl1 _ []	= []
scanl1 f (x:xs) = scanl f x xs

scanr :: (a -> b -> b) -> b -> [a] -> [b]
scanr f z []     = [z]
scanr f z (x:xs) = f x y : (y:ys)
  where (y:ys) = scanr f z xs

scanr1 :: (a -> a -> a) -> [a] -> [a]
scanr1 f []     = []
scanr1 f (x:xs) = scanr1p f x xs
  where scanr1p f x  []	     = [x]
  	scanr1p f x1 (x2:xs) = f x1 y : (y:ys)
	  where (y:ys) = scanr1p f x2 xs

cycle :: [a] -> [a]
cycle xs | not (null xs) = cycle' xs
  where cycle' xs = xs ++ cycle' xs

sum, product :: [Int] -> Int
sum = foldr (+) 0
product = foldr (*) 1

maximum, minimum :: [a] -> a
maximum xs = foldr1 max xs
minimum xs = foldr1 min xs

{- end of supposed Prelude functions -}

elemIndex :: a -> [a] -> Maybe Int
elemIndex x = findIndex (x ==)

elemIndices :: a -> [a] -> [Int]
elemIndices x = findIndices (x ==)

find :: (a -> Bool) -> [a] -> Maybe a
find _ [] = Nothing
find p (x:xs) = if p x then Just x else find p xs

findIndex :: (a -> Bool) -> [a] -> Maybe Int
findIndex p xs = listToMaybe (findIndices p xs)

findIndices :: (a -> Bool) -> [a] -> [Int]
findIndices p xs = [i | (i,x) <- zip [0..] xs, p x]

nub :: [a] -> [a]
nub = nubBy (==)

nubBy :: (a -> a -> Bool) -> [a] -> [a]
nubBy _ [] = []
nubBy p (x:xs) = x : nubBy p (filter (not . p x) xs)

delete :: a -> [a] -> [a]
delete = deleteBy (==)

deleteBy :: (a -> a -> Bool) -> a -> [a] -> [a]
deleteBy p x []     = []
deleteBy p x (y:ys) = if p x y then ys else y : deleteBy p x ys

(\\) :: [a] -> [a] -> [a]
(\\) = deleteFirstsBy (==)

deleteFirstsBy :: (a -> a -> Bool) -> [a] -> [a] -> [a]
deleteFirstsBy p xs ys = foldr (deleteBy p) ys xs

union :: [a] -> [a] -> [a]
union = unionBy (==)

unionBy :: (a -> a -> Bool) -> [a] -> [a] -> [a]
unionBy p xs ys = xs ++ deleteFirstsBy p xs ys

intersect :: [a] -> [a] -> [a]
intersect = intersectBy (==)

intersectBy :: (a -> a -> Bool) -> [a] -> [a] -> [a]
intersectBy p xs ys = [x | x <- xs, any (p x) ys]

intersperse :: a -> [a] -> [a]
intersperse _ []     = []
intersperse s (x:xs) = interspersep s x xs
  where interspersep _ x  []      = [x]
  	interspersep s x1 (x2:xs) = x1 : s : interspersep s x2 xs

transpose :: [[a]] -> [[a]]
transpose [] 	     = []
transpose ([] : xss) = transpose xss
transpose ((x:xs) : xss) =
  (x : [h | (h:t) <- xss]) : transpose (xs : [t | (h:t) <- xss])

partition :: (a -> Bool) -> [a] -> ([a],[a])
partition p xs = foldr (select p) ([],[]) xs
  where select p x rest = if p x then ((x:ys),zs) else (ys,(x:zs))
	  where (ys,zs) = rest

group :: [a] -> [[a]]
group = groupBy (==)

groupBy :: (a -> a -> Bool) -> [a] -> [[a]]
groupBy p []     = []
groupBy p (x:xs) = (x:ys) : groupBy p zs
  where (ys,zs) = span (p x) xs

inits :: [a] -> [[a]]
inits []     = [[]]
inits (x:xs) = [] : map (x:) (inits xs)

tails :: [a] -> [[a]]
tails []         = [[]]
tails xs@(_:xs') = xs : tails xs'

isPrefixOf :: [a] -> [a] -> Bool
isPrefixOf []     _      = True
isPrefixOf (_:_)  []     = False
isPrefixOf (x:xs) (y:ys) = x == y && isPrefixOf xs ys

isSuffixOf :: [a] -> [a] -> Bool
isSuffixOf xs ys = isPrefixOf (reverse xs) (reverse ys)

mapAccumL :: (a -> b -> (a,c)) -> a -> [b] -> (a,[c])
mapAccumL f z []     = (z,[])
mapAccumL f z (x:xs) = (z'',y:ys)
  where (z',y)   = f z x
        (z'',ys) = mapAccumL f z' xs

mapAccumR :: (a -> b -> (a,c)) -> a -> [b] -> (a,[c])
mapAccumR f z []     = (z,[])
mapAccumR f z (x:xs) = (z'',y:ys)
  where (z'',y) = f z' x
        (z',ys) = mapAccumR f z xs

unfoldr :: (b -> Maybe (a,b)) -> b -> [a]
unfoldr f z =
  case f z of
    Nothing -> []
    Just (x,z) -> x : unfoldr f z

sort :: [a] -> [a]
sort = sortBy compare

sortBy :: (a -> a -> Ordering) -> [a] -> [a]
sortBy cmp xs = sort (split xs)
  where split [] = []
	split (x:xs) = [x] : split xs

	sort [] = []
	sort [xs] = xs
	sort xss@(_:_:_) = sort (merge xss)

	merge [] = []
	merge [xs] = [xs]
	merge (xs:ys:xss) = merge2 xs ys : merge xss

	merge2 [] [] = []
	merge2 [] (y:ys) = y:ys
	merge2 (x:xs) [] = x:xs
	merge2 (x:xs) (y:ys) =
	  case cmp x y of
	    GT -> y : merge2 (x:xs) ys
	    _  -> x : merge2 xs (y:ys)


insert :: a -> [a] -> [a]
insert = insertBy compare

insertBy :: (a -> a -> Ordering) -> a -> [a] -> [a]
insertBy cmp x []	  = [x]
insertBy cmp x (y:ys) =
  case cmp x y of
    GT -> y : insertBy cmp x ys
    _  -> x : y : ys

maximumBy :: (a -> a -> Ordering) -> [a] -> a
maximumBy cmp (x:xs) = foldr max x xs
  where max x y =
          case cmp x y of
	    LT -> y
	    _  -> x

minimumBy :: (a -> a -> Ordering) -> [a] -> a
minimumBy cmp (x:xs) = foldr min x xs
  where min x y =
          case cmp x y of
	    GT -> y
	    _  -> x

zip4 :: [a] -> [b] -> [c] -> [d] -> [(a,b,c,d)]
zip4 = zipWith4 (\w x y z -> (w,x,y,z))

zip5 :: [a] -> [b] -> [c] -> [d] -> [e] -> [(a,b,c,d,e)]
zip5 = zipWith5 (\v w x y z -> (v,w,x,y,z))

zip6 :: [a] -> [b] -> [c] -> [d] -> [e] -> [f] -> [(a,b,c,d,e,f)]
zip6 = zipWith6 (\u v w x y z -> (u,v,w,x,y,z))

zip7 :: [a] -> [b] -> [c] -> [d] -> [e] -> [f] -> [g] -> [(a,b,c,d,e,f,g)]
zip7 = zipWith7 (\t u v w x y z -> (t,u,v,w,x,y,z))

zipWith4 :: (a -> b -> c -> d -> (a,b,c,d))
	 -> [a] -> [b] -> [c] -> [d] -> [(a,b,c,d)]
zipWith4 _ []     _      _      _      = []
zipWith4 _ (_:_)  []     _      _      = []
zipWith4 _ (_:_)  (_:_)  []     _      = []
zipWith4 _ (_:_)  (_:_)  (_:_)  []     = []
zipWith4 f (w:ws) (x:xs) (y:ys) (z:zs) = f w x y z : zipWith4 f ws xs ys zs

zipWith5 :: (a -> b -> c -> d -> e -> (a,b,c,d,e))
	 -> [a] -> [b] -> [c] -> [d] -> [e] -> [(a,b,c,d,e)]
zipWith5 _ []     _      _      _      _      = []
zipWith5 _ (_:_)  []     _      _      _      = []
zipWith5 _ (_:_)  (_:_)  []     _      _      = []
zipWith5 _ (_:_)  (_:_)  (_:_)  []     _      = []
zipWith5 _ (_:_)  (_:_)  (_:_)  (_:_)  []     = []
zipWith5 f (v:vs) (w:ws) (x:xs) (y:ys) (z:zs) =
  f v w x y z : zipWith5 f vs ws xs ys zs

zipWith6 :: (a -> b -> c -> d -> e -> f -> (a,b,c,d,e,f))
	 -> [a] -> [b] -> [c] -> [d] -> [e] -> [f] -> [(a,b,c,d,e,f)]
zipWith6 _ []     _      _      _      _      _      = []
zipWith6 _ (_:_)  []     _      _      _      _      = []
zipWith6 _ (_:_)  (_:_)  []     _      _      _      = []
zipWith6 _ (_:_)  (_:_)  (_:_)  []     _      _      = []
zipWith6 _ (_:_)  (_:_)  (_:_)  (_:_)  []     _      = []
zipWith6 _ (_:_)  (_:_)  (_:_)  (_:_)  (_:_)  []     = []
zipWith6 f (u:us) (v:vs) (w:ws) (x:xs) (y:ys) (z:zs) =
  f u v w x y z : zipWith6 f us vs ws xs ys zs

zipWith7 :: (a -> b -> c -> d -> e -> f -> g -> (a,b,c,d,e,f,g))
	 -> [a] -> [b] -> [c] -> [d] -> [e] -> [f] -> [g] -> [(a,b,c,d,e,f,g)]
zipWith7 _ []     _      _      _      _      _      _      = []
zipWith7 _ (_:_)  []     _      _      _      _      _      = []
zipWith7 _ (_:_)  (_:_)  []     _      _      _      _      = []
zipWith7 _ (_:_)  (_:_)  (_:_)  []     _      _      _      = []
zipWith7 _ (_:_)  (_:_)  (_:_)  (_:_)  []     _      _      = []
zipWith7 _ (_:_)  (_:_)  (_:_)  (_:_)  (_:_)  []     _      = []
zipWith7 _ (_:_)  (_:_)  (_:_)  (_:_)  (_:_)  (_:_)  []     = []
zipWith7 f (t:ts) (u:us) (v:vs) (w:ws) (x:xs) (y:ys) (z:zs) =
  f t u v w x y z : zipWith7 f ts us vs ws xs ys zs

unzip4 :: [(a,b,c,d)] -> ([a],[b],[c],[d])
unzip4 []	      = ([],[],[],[])
unzip4 ((w,x,y,z):rs) = ((w:ws),(x:xs),(y:ys),(z:zs))
  where (ws,xs,ys,zs) = unzip4 rs

unzip5 :: [(a,b,c,d,e)] -> ([a],[b],[c],[d],[e])
unzip5 []		= ([],[],[],[],[])
unzip5 ((v,w,x,y,z):rs) = ((v:vs),(w:ws),(x:xs),(y:ys),(z:zs))
  where (vs,ws,xs,ys,zs) = unzip5 rs

unzip6 :: [(a,b,c,d,e,f)] -> ([a],[b],[c],[d],[e],[f])
unzip6 []		  = ([],[],[],[],[],[])
unzip6 ((u,v,w,x,y,z):rs) = ((u:us),(v:vs),(w:ws),(x:xs),(y:ys),(z:zs))
  where (us,vs,ws,xs,ys,zs) = unzip6 rs

unzip7 :: [(a,b,c,d,e,f,g)] -> ([a],[b],[c],[d],[e],[f],[g])
unzip7 []		    = ([],[],[],[],[],[],[])
unzip7 ((t,u,v,w,x,y,z):rs) =
  ((t:ts),(u:us),(v:vs),(w:ws),(x:xs),(y:ys),(z:zs))
  where (ts,us,vs,ws,xs,ys,zs) = unzip7 rs
