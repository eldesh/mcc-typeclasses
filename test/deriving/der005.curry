-- Instances cannot be derived for types with existentially quantified
-- types. In principle, it would be possible to derive instances in some
-- special cases, e.g., 
--   data T = forall a . Show a => T a deriving (Show)
-- or
--   data U a = Eq a => U a a deriving (Eq,Ord)
-- In particular, instances of Eq, Ord, and Show could be derived when
-- all existentially quantified type variables are instances of that
-- class as well. Instance of Bounded, Enum, Read, and Ix can never be
-- derived in the presence of existential type variables.

-- possible in principle, but not (yet) supported
data T = forall a . Show a => T a deriving (Show)
  
-- impossible (skolem would escape minBound and maxBound types)
data B = forall a . Bounded a => B a deriving (Bounded)

-- special case; the Eq (U a) context would not require a Eq a
-- context. However, the compiler at present doesn't notice this.
data U a = Eq a => U a a deriving (Eq,Ord)
f :: U a -> Bool
f (U x y) = x == y
