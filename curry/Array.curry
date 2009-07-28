module Array(module Ix,    -- export all of Ix for convenience
       	     Array, array, listArray, (!), bounds, indices, elems, assocs,
	     accumArray, (//), accum, ixmap,
	     vectorArray, vector) where
import Ix
import IOVector
import Unsafe

infixl 9 !, //

data Array a = Array (Int,Int) (Vector a)

instance Eq a => Eq (Array a) where
  a1 == a2 = assocs a1 == assocs a2
instance Ord a => Ord (Array a) where
  a1 `compare` a2 = assocs a1 `compare` assocs a2
instance Show a => Show (Array a) where
  showsPrec p a =
    showParen (p > 10)
              (showString "array " . showsPrec 11 (bounds a) .
                      showChar ' ' . showsPrec 11 (assocs a))
instance Functor Array where
  fmap f a = listArray (bounds a) (map f (elems a))

array      :: (Int,Int) -> [(Int,a)] -> Array a
array b ixs = unsafePerformIO initArray
  where initArray = 
          do
            v <- newIOVector (rangeSize b) undefined
	    mapIO_ (\(i,x) -> writeIOVector v (index b i) x) ixs
	    v' <- unsafeFreezeIOVector v
	    return (Array b v')

listArray  :: (Int,Int) -> [a] -> Array a
listArray b xs = unsafePerformIO initArray
  where initArray =
	  do
            v <- newIOVector n undefined
	    mapIO_ (\(i,x) -> writeIOVector v i x) (take n (zip [0..] xs))
	    v' <- unsafeFreezeIOVector v
	    return (Array b v')
	  where n = rangeSize b

(!)	   :: Array a -> Int -> a
Array b v ! i = readVector v (index b i)

bounds     :: Array a -> (Int,Int)
bounds (Array b _) = b

indices    :: Array a -> [Int]
indices (Array b _) = range b

elems      :: Array a -> [a]
elems (Array b v) = map (readVector v) (take (rangeSize b) [0..])

assocs	   :: Array a -> [(Int,a)]
assocs a = zip (indices a) (elems a)

(//)       :: Array a -> [(Int,a)] -> Array a
Array b v // ixs = unsafePerformIO updateArray
  where updateArray =
          do
            v' <- thawIOVector v
	    mapIO_ (\(i,x) -> writeIOVector v' (index b i) x) ixs
	    v'' <- unsafeFreezeIOVector v'
	    return (Array b v'')

accum      :: (a -> b -> a) -> Array a -> [(Int,b)] -> Array a
accum f (Array b v) ixs = unsafePerformIO updateArray
  where updateArray =
          do
	    v' <- thawIOVector v
	    mapIO_ (update v') ixs
	    v'' <- unsafeFreezeIOVector v'
	    return (Array b v'')
  	update v (i,x) =
 	  do
 	    z <- readIOVector v j
	    writeIOVector v j (f z x)
	  where j = index b i

accumArray :: (a -> b -> a) -> a -> (Int,Int) -> [(Int,b)] -> Array a
accumArray f z b = accum f (array b [(i,z) | i <- range b])

ixmap	   :: (Int,Int) -> (Int -> Int) -> Array a -> Array a
ixmap b f a = listArray b [a ! f i | i <- range b]


-- vectorArray and vector are MCC extensions for converting vectors
-- into arrays and vice versa
vectorArray :: (Int,Int) -> Vector a -> Array a
vectorArray b v
  | rangeSize b == lengthVector v = Array b v
  | otherwise = error "internal error: vectorArray"

vector :: Array a -> Vector a
vector (Array _ v) = v
