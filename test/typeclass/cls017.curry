-- Here is a rather contrived example where the compiler may or may not
-- specialize the code so as to use the Int implementations of (==) and
-- (<) directly. This is because the compiler may be using the Eq Int and
-- Ord Int dictionaries that are available via the Set constructor's
-- context. If these dictionary arguments are used instead of the global
-- instances, the compiler is unable to determine the additional
-- arguments, if any, to which the (==) and (<) instance methods must be
-- applied and therefore it does not specialize the code.
-- 
-- Note: Actually, the compiler *might* specialize the code for this
-- particular example even when using the Set constructor's implicit
-- dictionaries by using the fact that the instance contexts of the Eq
-- Int and Ord Int instances are empty and therefore their respective
-- method implementations can take no additional dictionary arguments.

data Set a = Ord a => Set [a]

instance Show a => Show (Set a) where
  showsPrec p (Set xs) = showsPrec p xs

emptySet :: Ord a => Set a
emptySet = Set []

insertInt :: Int -> Set Int -> Set Int
insertInt x (Set xs) = Set (ys ++ ins x zs)
  where (ys,zs) = span (< x) xs
        ins x [] = [x]
	ins x (z:zs) = if x == z then x:zs else x:z:zs

main = print (foldr insertInt emptySet [1,9,5,4,2,9,7,3,6,8,3,2])
