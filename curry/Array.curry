-- $Id: Array.curry 2876 2009-07-28 08:46:16Z wlux $
--
-- Copyright (c) 2000-2009, Wolfgang Lux
-- See ../LICENSE for the full license.

module Array(module Ix,    -- export all of Ix for convenience
       	     Array, array, listArray, (!), bounds, indices, elems, assocs,
	     accumArray, (//), accum, ixmap,
	     vectorArray, vector) where
import Ix
import IOVector
import Unsafe

infixl 9 !, //

data Ix a => Array a b = Array (a,a) (Vector b)

instance (Ix a, Eq b) => Eq (Array a b) where
  a1 == a2 = assocs a1 == assocs a2
instance (Ix a, Ord b) => Ord (Array a b) where
  a1 `compare` a2 = assocs a1 `compare` assocs a2
instance (Ix a, Show a, Show b) => Show (Array a b) where
  showsPrec p a =
    showParen (p > 10)
              (showString "array " . showsPrec 11 (bounds a) .
                      showChar ' ' . showsPrec 11 (assocs a))
instance Ix a => Functor (Array a) where
  fmap f a = listArray (bounds a) (map f (elems a))

array      :: Ix a => (a,a) -> [(a,b)] -> Array a b
array b ixs = unsafePerformIO initArray
  where initArray = 
          do
            v <- newIOVector (rangeSize b) undefined
	    mapIO_ (\(i,x) -> writeIOVector v (index b i) x) ixs
	    v' <- unsafeFreezeIOVector v
	    return (Array b v')

listArray  :: Ix a => (a,a) -> [b] -> Array a b
listArray b xs = unsafePerformIO initArray
  where initArray =
	  do
            v <- newIOVector n undefined
	    mapIO_ (\(i,x) -> writeIOVector v i x) (take n (zip [0..] xs))
	    v' <- unsafeFreezeIOVector v
	    return (Array b v')
	  where n = rangeSize b

(!)	   :: Ix a => Array a b -> a -> b
Array b v ! i = readVector v (index b i)

bounds     :: Ix a => Array a b -> (a,a)
bounds (Array b _) = b

indices    :: Ix a => Array a b -> [a]
indices (Array b _) = range b

elems      :: Ix a => Array a b -> [b]
elems (Array b v) = map (readVector v) (take (rangeSize b) [0..])

assocs	   :: Ix a => Array a b -> [(a,b)]
assocs a = zip (indices a) (elems a)

(//)       :: Ix a => Array a b -> [(a,b)] -> Array a b
Array b v // ixs = unsafePerformIO updateArray
  where updateArray =
          do
            v' <- thawIOVector v
	    mapIO_ (\(i,x) -> writeIOVector v' (index b i) x) ixs
	    v'' <- unsafeFreezeIOVector v'
	    return (Array b v'')

accum      :: Ix a => (b -> c -> b) -> Array a b -> [(a,c)] -> Array a b
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

accumArray :: Ix a => (b -> c -> b) -> b -> (a,a) -> [(a,c)] -> Array a b
accumArray f z b = accum f (array b [(i,z) | i <- range b])

ixmap	   :: (Ix a,Ix b) => (a,a) -> (a -> b) -> Array b c -> Array a c
ixmap b f a = listArray b [a ! f i | i <- range b]

-- vectorArray and vector are MCC extensions for converting vectors
-- into arrays and vice versa
vectorArray :: Ix a => (a,a) -> Vector b -> Array a b
vectorArray b v
  | rangeSize b == lengthVector v = Array b v
  | otherwise = error "internal error: vectorArray"

vector :: Ix a => Array a b -> Vector b
vector (Array _ v) = v
