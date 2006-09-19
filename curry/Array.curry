module Array(module Ix,    -- export all of Ix for convenience
       	     Array, array, listArray, (!), bounds, indices, elems, assocs,
	     accumArray, (//), accum, ixmap, amap,
	     -- private exports for use in IOExts
	     unsafeVector, unsafeArray) where
import Ix
import IOVector
import Unsafe

infixl 9 !, //

data Array a = Array (Int,Int) (IOVector a)

array      :: (Int,Int) -> [(Int,a)] -> Array a
array b ixs = unsafePerformIO initArray
  where initArray = 
          do
            v <- newIOVector (rangeSize b) undefined
	    mapIO_ (\(i,x) -> writeIOVector v (index b i) x) ixs
	    return (Array b v)

listArray  :: (Int,Int) -> [a] -> Array a
listArray b xs = unsafePerformIO initArray
  where initArray =
	  do
            v <- newIOVector n undefined
	    mapIO_ (\(i,x) -> writeIOVector v i x) (take n (zip [0..] xs))
	    return (Array b v)
	  where n = rangeSize b

(!)	   :: Array a -> Int -> a
Array b v ! i = unsafePerformIO (readIOVector v (index b i))

bounds     :: Array a -> (Int,Int)
bounds (Array b _) = b

indices    :: Array a -> [Int]
indices (Array b _) = range b

elems      :: Array a -> [a]
elems (Array b v) = map (readArray v) (take (rangeSize b) [0..])
  where readArray v i = unsafePerformIO (readIOVector v i)

assocs	   :: Array a -> [(Int,a)]
assocs a = zip (indices a) (elems a)

(//)       :: Array a -> [(Int,a)] -> Array a
Array b v // ixs = unsafePerformIO updateArray
  where updateArray =
          do
            v' <- copyIOVector v
	    mapIO_ (\(i,x) -> writeIOVector v' (index b i) x) ixs
	    return (Array b v')

accum      :: (a -> b -> a) -> Array a -> [(Int,b)] -> Array a
accum f (Array b v) ixs = unsafePerformIO updateArray
  where updateArray =
          do
	    v' <- copyIOVector v
	    mapIO_ (update v') ixs
	    return (Array b v')
  	update v (i,x) =
 	  do
 	    z <- readIOVector v j
	    writeIOVector v j (f z x)
	  where j = index b i

accumArray :: (a -> b -> a) -> a -> (Int,Int) -> [(Int,b)] -> Array a
accumArray f z b = accum f (array b [(i,z) | i <- range b])

ixmap	   :: (Int,Int) -> (Int -> Int) -> Array a -> Array a
ixmap b f a = listArray b [a ! f i | i <- range b]

-- amap replace the functor instace of Haskell arrays
amap       :: (a -> b) -> Array a -> Array b
amap f a = listArray (bounds a) (map f (elems a))

-- these functions should be used only from the IOExts module
-- for implementing the conversion between Arrays and IOArrays
unsafeVector :: Array a -> IO (IOVector a)
unsafeVector (Array b v) = return v

unsafeArray :: (Int,Int) -> IOVector a -> IO (Array a)
unsafeArray b v
  | rangeSize b == lengthIOVector v = return (Array b v)
  | otherwise = error "internal error: fromVector"
