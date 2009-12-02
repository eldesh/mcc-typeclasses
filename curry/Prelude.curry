-- $Id: Prelude.curry 2921 2009-12-02 21:22:18Z wlux $
--
-- Copyright (c) 1999-2009, Wolfgang Lux
-- See ../LICENSE for the full license.

module Prelude((.), id, const, curry, uncurry, flip, until,
               seq, ensureNotFree, ensureGround, ensureSpine,
               ($), ($!), ($!!), ($#), ($##),
               error, undefined, failed,
               Eq(..), Ord(..), Enum(..), Bounded(..), Show(..),
               Functor(..), Monad(..),
               Bool(..), (&&), (||), not, if_then_else, otherwise,
               Ordering(..),
               fst, snd,
               head, tail, null, (++), length, (!!),
               map, foldl, foldl1, foldr, foldr1, filter,
               zip, zip3, zipWith, zipWith3, unzip, unzip3,
               concat, concatMap, iterate, repeat, replicate,
               take, drop, splitAt, takeWhile, dropWhile, span, break,
               reverse, and, or, any, all, elem, notElem, lookup,
               Char(), ord, chr,
               String, lines, unlines, words, unwords,
               ShowS, shows, showChar, showString, showParen,
               Num(..), Real(..), Integral(..), Fractional(..), RealFrac(..),
               Floating(..), RealFloat(..),
               subtract, even, odd, gcd, lcm, (^), (^^),
               fromIntegral, realToFrac,
               Int(), Integer(), Float(), Ratio(), Rational(),
               Success(), (=:=), (=/=), (=:<=), success, (&), (&>),
               Maybe(..), maybe,
               Either(..), either,
               IO(), done, sequence, sequence_, mapM, mapM_,
               sequenceIO, sequenceIO_, mapIO, mapIO_,
               getChar, getLine, getContents,
               putChar, putStr, putStrLn, print,
               FilePath, readFile, writeFile, appendFile,
               IOError, ioError, catch,
               interact, doSolve,
               (?), unknown,
               try, inject, solveAll, once, best, findall, findfirst,
               browse, browseList, unpack) where
import Ratio(Ratio, Rational, numerator, denominator)
import IO

-- Infix operator declarations:

infixl 9 !!
infixr 9 .
infixl 8 ^, ^^, **
infixl 7 *, /, `quot`, `rem`, `div`, `mod`
infixl 6 +, -
infixr 5 :, ++
infix  4 =:=, =/=, =:<=, ==, /=, <, >, <=, >=
infix  4 `elem`, `notElem`
infixr 3 &&
infixr 2 ||
infixl 1 >>, >>=
infixr 0 $, $!, $!!, $#, $##, `seq`, &, &>, ?

-- Some standard combinators:

--- The function arrow type
data (->) a b

--- Function composition.
(.)   :: (b -> c) -> (a -> b) -> (a -> c)
(f . g) x = f (g x)

--- Identity function.
id              :: a -> a
id x            = x

--- Constant function.
const           :: a -> b -> a
const x _       = x

--- Converts an uncurried function to a curried function.
curry           :: ((a,b) -> c) -> a -> b -> c
curry f a b     =  f (a,b)

--- Converts an curried function to a function on pairs.
uncurry         :: (a -> b -> c) -> (a,b) -> c
uncurry f (a,b) = f a b

--- (flip f) is identical to f but with the order of arguments reversed.
flip            :: (a -> b -> c) -> b -> a -> c
flip  f x y     = f y x

--- Repeat application of a function until a predicate holds.
until          :: (a -> Bool) -> (a -> a) -> a -> a
until p f x     = if p x then x else until p f (f x)


--- Evaluate the first argument to head normal form and return the
--- second argument.
foreign import primitive seq :: a -> b -> b

--- (ensureNotFree x) is equivalent to (id x) except that it suspends
--- until x is instantiated to a non-variable term.
foreign import primitive ensureNotFree :: a -> a

--- (ensureGround x) is equivalent to (id x) except that it ensures that the
--- result is a ground term.
foreign import primitive ensureGround :: a -> a


--- Right-associative application.
($)             :: (a -> b) -> a -> b
f $ x           = f x

--- Right-associative application with strict evaluation of its argument.
($!)		:: (a -> b) -> a -> b
f $! x		= x `seq` f x

--- Right-associative application with strict evaluation of its argument
--- to normal form.
($!!)		:: (a -> b) -> a -> b
f $!! x		| x=:=y = f y where y free

--- Right-associative application with strict evaluation of its argument
--- to a non-variable term.
($#)		:: (a -> b) -> a -> b
f $# x		= f $! ensureNotFree x

--- Right-associative application with strict evaluation of its argument
--- to ground normal form.
($##)		:: (a -> b) -> a -> b
f $## x		= f $!! ensureGround x


--- Abort the execution with an error message.
error :: String -> a
error msg = unsafePerformIO (abort ("Error: " ++ msg ++ "\n"))
  where abort msg = hPutStr stderr msg >> curry_exit 1 >> undefined
	foreign import primitive unsafePerformIO :: IO a -> a
 	foreign import ccall curry_exit :: Int -> IO ()
        -- NB curry_exit does not return and therefore should have
        --    type Int -> IO a, but this type is not a valid foreign
        --    type for the ccall calling convention.

--- The totally undefined function.
foreign import primitive "failed" undefined :: a


--- failed is a non-reducible polymorphic function.
--- It is useful to express a failure in a search branch of the execution.
foreign import primitive failed :: a


--- Standard classes

--- Equality and Ordered classes

class Eq a where
  (==) :: a -> a -> Bool
  (/=) :: a -> a -> Bool

  -- Minimal complete definition:
  -- (==) or (/=)
  x /= y = not (x == y)
  x == y = not (x /= y)

class Eq a => Ord a where
  compare              :: a -> a -> Ordering
  (<), (<=), (>=), (>) :: a -> a -> Bool
  min, max             :: a -> a -> a

  -- Minimal complete definition:
  -- (<=) or compare
  -- Using compare can be more efficient for complex types
  compare x y
    | x == y = EQ
    | x <= y = LT
    | otherwise = GT

  x <= y = case compare x y of GT -> False; _ -> True
  x < y  = case compare x y of LT -> True; _ -> False
  x > y  = case compare x y of GT -> True; _ -> False
  x >= y = case compare x y of LT -> False; _ -> True

  -- note that (min x y, max x y) = (x,y) or (y,x)
  max x y = if x <= y then y else x
  min x y = if x <= y then x else y

--- Enumeration and Bounded classes

class Enum a where
  succ, pred 	 :: a -> a
  toEnum     	 :: Int -> a
  fromEnum   	 :: a -> Int
  enumFrom   	 :: a -> [a]
  enumFromThen   :: a -> a -> [a]
  enumFromTo     :: a -> a -> [a]
  enumFromThenTo :: a -> a -> a -> [a]

  -- Minimal complete definition:
  -- toEnum, fromEnum

  -- NB These default methods only make sense for types that
  --    map injectively into Int using fromEnum and toEnum
  succ x = toEnum (fromEnum x + 1)
  pred x = toEnum (fromEnum x - 1)
  enumFrom x           = map toEnum [fromEnum x ..]
  enumFromTo x y       = map toEnum [fromEnum x .. fromEnum y]
  enumFromThen x y     = map toEnum [fromEnum x, fromEnum y ..]
  enumFromThenTo x y z = map toEnum [fromEnum x, fromEnum y .. fromEnum z]

class Bounded a where
  minBound :: a
  maxBound :: a

--- Show class
class Show a where
  showsPrec :: Int -> a -> ShowS
  show      :: a -> String
  showList  :: [a] -> ShowS

  -- Minimal complete definition:
  -- show or showsPrec
  showsPrec _ x s = show x ++ s
  show x          = showsPrec 0 x ""
  showList []     = showString "[]"
  showList (x:xs) = showChar '[' . shows x . showl xs
    where showl []     = showChar ']'
          showl (x:xs) = showChar ',' . shows x . showl xs


-- Monadic classes

class Functor f where
  fmap :: (a -> b) -> f a -> f b

class Monad m where
  return :: a -> m a
  (>>=)  :: m a -> (a -> m b) -> m b
  (>>)   :: m a -> m b -> m b
  fail   :: String -> m a

  -- Minimal complete definition:
  -- return, (>>=)
  m >> k = m >>= \_ -> k
  fail s = error s


-- Boolean values
-- already defined as builtin, since it is required for if-then-else
data Bool = False | True deriving (Eq,Ord,Enum,Show,Bounded)

--- Sequential conjunction on Booleans.
(&&)            :: Bool -> Bool -> Bool
True  && x      = x
False && _      = False

--- Sequential disjunction on Booleans.
(||)            :: Bool -> Bool -> Bool
True  || _      = True
False || x      = x

--- Negation.
not             :: Bool -> Bool
not True        = False
not False       = True

--- Conditional.
if_then_else	:: Bool -> a -> a -> a
if_then_else b t f =
  case b of 
    True -> t
    False -> f

--- Useful name for the last condition in a sequence of conditional equations.
otherwise       :: Bool
otherwise       = True


-- Ordering
data Ordering = LT | EQ | GT deriving (Eq,Ord,Enum,Show,Bounded)


-- Tuples

data (,) a b = (,) a b deriving(Eq,Ord,Bounded)
data (,,) a b c = (,,) a b c deriving(Eq,Ord,Bounded)
data (,,,) a b c d = (,,,) a b c d deriving(Eq,Ord,Bounded)
data (,,,,) a b c d e = (,,,,) a b c d e deriving(Eq,Ord,Bounded)
data (,,,,,) a b c d e f = (,,,,,) a b c d e f deriving(Eq,Ord,Bounded)
data (,,,,,,) a b c d e f g = (,,,,,,) a b c d e f g deriving(Eq,Ord,Bounded)
data (,,,,,,,) a b c d e f g h = (,,,,,,,) a b c d e f g h
data (,,,,,,,,) a b c d e f g h i = (,,,,,,,,) a b c d e f g h i
data (,,,,,,,,,) a b c d e f g h i j = (,,,,,,,,,) a b c d e f g h i j
data (,,,,,,,,,,) a b c d e f g h i j k = (,,,,,,,,,,) a b c d e f g h i j k
data (,,,,,,,,,,,) a b c d e f g h i j k l =
  (,,,,,,,,,,,) a b c d e f g h i j k l
data (,,,,,,,,,,,,) a b c d e f g h i j k l m =
  (,,,,,,,,,,,,) a b c d e f g h i j k l m
data (,,,,,,,,,,,,,) a b c d e f g h i j k l m n =
  (,,,,,,,,,,,,,) a b c d e f g h i j k l m n
data (,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o =
  (,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o
data (,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p =
  (,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p
data (,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q =
  (,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q
data (,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r =
  (,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r
data (,,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r s =
  (,,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r s
data (,,,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r s t =
  (,,,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r s t
data (,,,,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r s t u =
  (,,,,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r s t u
data (,,,,,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r s t u v =
  (,,,,,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r s t u v
data (,,,,,,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r s t u v w =
  (,,,,,,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r s t u v w
data (,,,,,,,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r s t u v w x =
  (,,,,,,,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r s t u v w x
data (,,,,,,,,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r s t u v w x y =
  (,,,,,,,,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r s t u v w x y
data (,,,,,,,,,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r s t u v w x y z =
  (,,,,,,,,,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r s t u v w x y z
data (,,,,,,,,,,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r s t u v w x y z a1 =
  (,,,,,,,,,,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r s t u v w x y z a1
data (,,,,,,,,,,,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r s t u v w x y z a1 b1 =
  (,,,,,,,,,,,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r s t u v w x y z a1 b1
data (,,,,,,,,,,,,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r s t u v w x y z a1 b1 c1 =
  (,,,,,,,,,,,,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r s t u v w x y z a1 b1 c1
data (,,,,,,,,,,,,,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r s t u v w x y z a1 b1 c1 d1 =
  (,,,,,,,,,,,,,,,,,,,,,,,,,,,,,) a b c d e f g h i j k l m n o p q r s t u v w x y z a1 b1 c1 d1
instance (Show a,Show b) => Show (a,b) where
  showsPrec _ (x1,x2) =
    showChar '(' . shows x1 . showChar ',' . shows x2 . showChar ')'
instance (Show a,Show b,Show c) => Show (a,b,c) where
  showsPrec _ (x1,x2,x3) =
    showChar '(' . shows x1 . showChar ',' .
                   shows x2 . showChar ',' .
                   shows x3 . showChar ')'
instance (Show a,Show b,Show c,Show d) => Show (a,b,c,d) where
  showsPrec _ (x1,x2,x3,x4) =
    showChar '(' . shows x1 . showChar ',' .
                   shows x2 . showChar ',' .
                   shows x3 . showChar ',' .
                   shows x4 . showChar ')'
instance (Show a,Show b,Show c,Show d,Show e) => Show (a,b,c,d,e) where
  showsPrec _ (x1,x2,x3,x4,x5) =
    showChar '(' . shows x1 . showChar ',' .
                   shows x2 . showChar ',' .
                   shows x3 . showChar ',' .
                   shows x4 . showChar ',' .
                   shows x5 . showChar ')'
instance (Show a,Show b,Show c,Show d,Show e,Show f) => Show (a,b,c,d,e,f) where
  showsPrec _ (x1,x2,x3,x4,x5,x6) =
    showChar '(' . shows x1 . showChar ',' .
                   shows x2 . showChar ',' .
                   shows x3 . showChar ',' .
                   shows x4 . showChar ',' .
                   shows x5 . showChar ',' .
                   shows x6 . showChar ')'
instance (Show a,Show b,Show c,Show d,Show e,Show f,Show g) => Show (a,b,c,d,e,f,g) where
  showsPrec _ (x1,x2,x3,x4,x5,x6,x7) =
    showChar '(' . shows x1 . showChar ',' .
                   shows x2 . showChar ',' .
                   shows x3 . showChar ',' .
                   shows x4 . showChar ',' .
                   shows x5 . showChar ',' .
                   shows x6 . showChar ',' .
                   shows x7 . showChar ')'

--- Selects the first component of a pair.
fst             :: (a,b) -> a
fst (x,_)       = x

--- Selects the second component of a pair.
snd             :: (a,b) -> b
snd (_,y)       = y


-- Unit type
data () = () deriving(Eq,Ord,Bounded)
instance Enum () where
  pred () = failed
  succ () = failed
  toEnum 0 = ()
  fromEnum () = 0
  enumFrom () = [()]
  enumFromTo () () = [()]
  enumFromThen () () = repeat ()
  enumFromThenTo () () () = repeat ()
instance Show () where
  showsPrec _ () = showString "()"


-- Lists

data [] a = [] | a : [a] deriving(Eq,Ord)
instance Show a => Show [a] where
  showsPrec _ = showList
instance Functor [] where
  fmap = map
instance Monad [] where
  return x = [x]
  xs >>= f = concatMap f xs
  fail _   = []


--- Evaluates the argument to spine form and returns it.
--- Suspends until the result is bound to a non-variable spine.
ensureSpine    	 :: [a] -> [a]
ensureSpine l =
  case l of
     []   -> []
     x:xs -> x : ensureSpine xs

--- Computes the first element of a list.
head            :: [a] -> a
head (x:_)      = x

--- Computes the remaining elements of a list.
tail            :: [a] -> [a]
tail (_:xs)     = xs

--- Is a list empty?
null            :: [a] -> Bool
null []         = True
null (_:_)      = False

--- Concatenates two lists.
(++)            :: [a] -> [a] -> [a]
[]     ++ ys    = ys
(x:xs) ++ ys    = x : xs++ys

--- Computes the length of a list.
length          :: [a] -> Int
length		= count 0
  where count :: Int -> [a] -> Int
        count n []     = n
  	count n (_:xs) = n' `seq` count n' xs where n' = n + 1

--- List index (subscript) operator, head has index 0
(!!)              :: [a] -> Int -> a
(x:xs) !! n
  | n == 0        = x
  | n > 0         = xs !! (n-1)

--- Map a function on all elements of a list.
map             :: (a -> b) -> [a] -> [b]
map _ []        = []
map f (x:xs)    = f x : map f xs

--- Accumulates all list elements by applying a binary operator from
--- left to right. Thus,
--- <CODE>foldl f z [x1,x2,...,xn] = (...((z `f` x1) `f` x2) ...) `f` xn</CODE>
foldl            :: (a -> b -> a) -> a -> [b] -> a
foldl _ z []     = z
foldl f z (x:xs) = foldl f (f z x) xs

--- Accumulates a non-empty list from left to right.
foldl1           :: (a -> a -> a) -> [a] -> a
foldl1 f (x:xs)  = foldl f x xs

--- Accumulates all list elements by applying a binary operator from
--- right to left. Thus,
--- <CODE>foldr f z [x1,x2,...,xn] = (x1 `f` (x2 `f` ... (xn `f` z)...))</CODE>
foldr            :: (a -> b -> b) -> b -> [a] -> b
foldr _ z []     = z
foldr f z (x:xs) = f x (foldr f z xs)

--- Accumulates a non-empty list from right to left:
foldr1              :: (a -> a -> a) -> [a] -> a
foldr1 _ [x]        = x
foldr1 f (x1:x2:xs) = f x1 (foldr1 f (x2:xs))

--- Filters all elements satisfying a given predicate in a list.
filter            :: (a -> Bool) -> [a] -> [a]
filter _ []       = []
filter p (x:xs)   = if p x then x : filter p xs
                           else filter p xs

--- Joins two lists into one list of pairs. If one input list is shorter than
--- the other, the additional elements of the longer list are discarded.
zip               :: [a] -> [b] -> [(a,b)]
zip		  = zipWith (,)

--- Joins three lists into one list of triples. If one input list is shorter
--- than the other, the additional elements of the longer lists are discarded.
zip3              :: [a] -> [b] -> [c] -> [(a,b,c)]
zip3		  = zipWith3 (,,)

--- Joins two lists into one list by applying a combination function to
--- corresponding pairs of elements. Thus <CODE>zip = zipWith (,)</CODE>
zipWith                 :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith _ []     _      = []
zipWith _ (_:_)  []     = []
zipWith f (x:xs) (y:ys) = f x y : zipWith f xs ys

--- Joins three lists into one list by applying a combination function to
--- corresponding triples of elements. Thus <CODE>zip3 = zipWith3 (,,)</CODE>
zipWith3	  :: (a -> b -> c -> d) -> [a] -> [b] -> [c] -> [d]
zipWith3 _ []     _      _      = []
zipWith3 _ (_:_)  []     _      = []
zipWith3 _ (_:_)  (_:_)  []     = []
zipWith3 f (x:xs) (y:ys) (z:zs) = f x y z : zipWith3 f xs ys zs

--- Transforms a list of pairs into a pair of lists.
unzip               :: [(a,b)] -> ([a],[b])
unzip []            = ([],[])
unzip ((x,y):ps)    = (x:xs,y:ys) where (xs,ys) = unzip ps

--- Transforms a list of triples into a triple of lists.
unzip3              :: [(a,b,c)] -> ([a],[b],[c])
unzip3 []           = ([],[],[])
unzip3 ((x,y,z):ts) = (x:xs,y:ys,z:zs) where (xs,ys,zs) = unzip3 ts

--- Concatenates a list of lists into one list.
concat            :: [[a]] -> [a]
concat l          = foldr (++) [] l

--- Maps a function from elements to lists and merges the result into one list.
concatMap         :: (a -> [b]) -> [a] -> [b]
concatMap f xs    = concat (map f xs)

--- Infinite list of repeated applications of a function f to an element x.
--- Thus, <CODE>iterate f x = [x, f x, f (f x),...]</CODE>
iterate           :: (a -> a) -> a -> [a]
iterate f x       = x : iterate f (f x)

--- Infinite list where all elements have the same value.
--- Thus, <CODE>repeat x = [x, x, x,...]</CODE>
repeat            :: a -> [a]
repeat x          = x : repeat x

--- List of length n where all elements have the same value.
replicate         :: Int -> a -> [a]
replicate n x     = take n (repeat x)

--- Returns prefix of length n.
take              :: Int -> [a] -> [a]
take n l          = if n<=0 then [] else takep n l
   where takep _ []     = []
         takep n (x:xs) = x : take (n-1) xs

--- Returns suffix without first n elements.
drop              :: Int -> [a] -> [a]
drop n l          = if n<=0 then l else dropp n l
   where dropp _ []     = []
         dropp n (_:xs) = drop (n-1) xs

--- (splitAt n xs) is equivalent to (take n xs, drop n xs)
splitAt		  :: Int -> [a] -> ([a],[a])
splitAt n l	  = if n <= 0 then ([],l) else splitAtp n l
  where splitAtp _ []     = ([],[])
	splitAtp n (x:xs) = let (ys,zs) = splitAt (n-1) xs in (x:ys,zs)

--- Returns longest prefix with elements satisfying a predicate.
takeWhile          :: (a -> Bool) -> [a] -> [a]
takeWhile _ []     = []
takeWhile p (x:xs) = if p x then x : takeWhile p xs else []

--- Returns suffix without takeWhile prefix.
dropWhile          :: (a -> Bool) -> [a] -> [a]
dropWhile _ []     = []
dropWhile p (x:xs) = if p x then dropWhile p xs else x:xs

--- (span p xs) is equivalent to (takeWhile p xs, dropWhile p xs)
span               :: (a -> Bool) -> [a] -> ([a],[a])
span _ []          = ([],[])
span p (x:xs)
  | p x	      = let (ys,zs) = span p xs in (x:ys,zs)
  | otherwise = ([],x:xs)

--- (break p xs) is equivalent to (takeWhile (not.p) xs, dropWhile (not.p) xs).
--- Thus, it breaks a list at the first occurrence of an element satisfying p.
break              :: (a -> Bool) -> [a] -> ([a],[a])
break p            = span (not . p)

--- Reverses the order of all elements in a list.
reverse    :: [a] -> [a]
reverse    = foldl (flip (:)) []

--- Computes the conjunction of a Boolean list.
and        :: [Bool] -> Bool
and []     = True
and (x:xs) = if x then and xs else False

--- Computes the disjunction of a Boolean list.
or         :: [Bool] -> Bool
or []      = False
or (x:xs)  = if x then True else or xs

--- Is there an element in a list satisfying a given predicate?
any        :: (a -> Bool) -> [a] -> Bool
any p xs   = or (map p xs)

--- Is a given predicate satisfied by all elements in a list?
all        :: (a -> Bool) -> [a] -> Bool
all p xs   = and (map p xs)

--- Element of a list?
elem       :: Eq a => a -> [a] -> Bool
elem x     = any (x==)

--- Not element of a list?
notElem    :: Eq a => a -> [a] -> Bool
notElem x  = all (x/=)

--- Looks up a key in an association list
lookup		     :: Eq a => a -> [(a,b)] -> Maybe b
lookup x []	     = Nothing
lookup x ((y,z):yzs) = if x == y then Just z else lookup x yzs



-- character type

-- Characters
data Char
instance Eq Char where
  (==) = primEqChar
    where foreign import ccall "prims.h" primEqChar :: Char -> Char -> Bool
  (/=) = primNeqChar
    where foreign import ccall "prims.h" primNeqChar :: Char -> Char -> Bool
instance Ord Char where
  (<) = primLtChar
    where foreign import ccall "prims.h" primLtChar :: Char -> Char -> Bool
  (<=) = primLeqChar
    where foreign import ccall "prims.h" primLeqChar :: Char -> Char -> Bool
  (>=) = primGeqChar
    where foreign import ccall "prims.h" primGeqChar :: Char -> Char -> Bool
  (>) = primGtChar
    where foreign import ccall "prims.h" primGtChar :: Char -> Char -> Bool
instance Enum Char where
  pred x | x > minBound = primPredChar x
    where foreign import ccall "prims.h" primPredChar :: Char -> Char
  succ x | x < maxBound = primSuccChar x
    where foreign import ccall "prims.h" primSuccChar :: Char -> Char
  toEnum = primChr
    where foreign import ccall "prims.h" primChr :: Int -> Char
  fromEnum = primOrd
    where foreign import ccall "prims.h" primOrd :: Char -> Int
  enumFrom c = enumFromTo c maxBound
  enumFromThen c1 c2 =
    enumFromThenTo c1 c2 (if c1 <= c2 then maxBound else minBound)
instance Bounded Char where
  minBound = primMinChar
    where foreign import ccall "prims.h" primMinChar :: Char
  maxBound = primMaxChar
    where foreign import ccall "prims.h" primMaxChar :: Char
instance Show Char where
  -- FIXME: use a dedicated primitive for this (if at all)
  showsPrec _ = shows where foreign import primitive shows :: a -> ShowS
  showList cs = if null cs then showString "\"\"" else shows cs
    where foreign import primitive shows :: a -> ShowS

--- Converts a characters into its ASCII value.
foreign import ccall "prims.h primOrd" ord :: Char -> Int

--- Converts an ASCII value into a character.
foreign import ccall "prims.h primChr" chr :: Int -> Char


-- Strings

type String = [Char]

--- Breaks a string into a list of lines where a line is terminated at a
--- newline character. The resulting lines do not contain newline characters.
lines        :: String -> [String]
lines []     = []
lines (c:cs) = l : lines' s'
  where (l,s') = break ('\n' ==) (c:cs)
	lines' []    = []
	lines' (_:s'') = lines s''

--- Concatenates a list of strings with terminating newlines.
unlines    :: [String] -> String
unlines ls = concatMap (++ "\n") ls

--- Breaks a string into a list of words where the words are delimited by
--- white spaces.
words      :: String -> [String]
words cs   =
  case dropWhile isSpace cs of
    "" -> []
    cs' -> let (w,cs'') = break isSpace cs' in w : words cs''
  where isSpace c = c `elem` " \t\n\r\f\v\xA0"

--- Concatenates a list of strings with a blank between two strings.
unwords    	:: [String] -> String
unwords []	 = []
unwords (w:ws) = w ++ foldr (\w cs -> (' ' : w) ++ cs) "" ws

--- Converts an arbitrary term into an external string representation.
type ShowS = String -> String

shows :: Show a => a -> ShowS
shows = showsPrec 0

showChar :: Char -> ShowS
showChar c = (c :)

showString :: String -> ShowS
showString s = (s ++)

showParen :: Bool -> ShowS -> ShowS
showParen True x = showChar '(' . x . showChar ')'
showParen False x = x


--- Standard numeric types and classes
class (Eq a, Show a) => Num a where
  (+) :: a -> a -> a
  (-) :: a -> a -> a
  (*) :: a -> a -> a
  negate :: a -> a
  abs, signum :: a -> a
  fromInt :: Int -> a                  -- NB non-standard addition
  fromInteger :: Integer -> a

  -- Minimal complete definition:
  -- All except fromInt and either negate or (-)
  x - y    = x + negate y
  negate x = 0 - x
  fromInt n = fromIntegral n

class (Ord a, Num a) => Real a where
  toRational :: a -> Rational

class (Enum a, Real a) => Integral a where
  -- quot, rem, div, and mod must satisfy the following laws
  -- N `quot` M + N `rem` M = N
  -- N `div`  M + N `mod` M = N
  -- the result of quot is truncated towards zero and the result
  -- of div is truncated towards negative infinity
  quot, rem :: a -> a -> a
  div, mod :: a -> a -> a
  quotRem, divMod :: a -> a -> (a,a)
  toInt :: a -> Int                    -- NB non-standard addition
  toInteger :: a -> Integer

  -- Minimal complete definition:
  -- quotRem, toInteger
  n `quot` d = case quotRem n d of (q,r) -> q
  n `rem` d  = case quotRem n d of (q,r) -> r
  n `div` d  = case divMod n d of (q,r) -> q
  n `mod` d  = case divMod n d of (q,r) -> r
  divMod n d =
    case quotRem n d of
      qr@(q,r) -> if signum r == - signum d then (q - 1, r + d) else qr
  toInt n = fromIntegral n

class Num a => Fractional a where
  (/) :: a -> a -> a
  recip :: a -> a
  fromRational :: Rational -> a
  fromFloat :: Float -> a              -- NB non-standard addition

  -- Minimal complete definition:
  -- fromRational and either recip or (/)
  recip x = 1 / x
  x / y   = x * recip y
  fromFloat f = realToFrac f

class (Real a, Fractional a) => RealFrac a where
  properFraction  :: Integral b => a -> (b,a)
  truncate, round :: Integral b => a -> b
  ceiling, floor  :: Integral b => a -> b

  -- Minimal complete definition:
  -- properFraction
  truncate x = case properFraction x of (n,_) -> n
  round x =
    case properFraction x of
      (n,r) ->
        if s == -1 || s == 0 && n `rem` 2 == 0
          then n
	  else if r < 0 then n - 1 else n + 1
        where s = signum (abs r - 0.5)
  ceiling x = case properFraction x of (n,r) -> if r > 0 then n + 1 else n
  floor x   = case properFraction x of (n,r) -> if r < 0 then n - 1 else n

class Fractional a => Floating a where
  pi                  :: a
  exp, log, sqrt      :: a -> a
  (**), logBase       :: a -> a -> a
  sin, cos, tan       :: a -> a
  asin, acos, atan    :: a -> a
  sinh, cosh, tanh    :: a -> a
  asinh, acosh, atanh :: a -> a

  -- Minimal complete definition:
  -- pi, exp, log, sin, cos, sinh, cosh, asin, acos, atan, asinh, acosh, atanh
  x ** y = exp (log x * y)
  logBase x y = log y / log x
  sqrt x = x ** 0.5
  tan  x = sin x / cos x
  tanh x = sinh x / cosh x

class (RealFrac a, Floating a) => RealFloat a where
  -- FIXME This class is grossly incomplete
  atan2 :: a -> a -> a
  toFloat :: a -> Float                -- NB non-standard addition

  -- Minimal complete definition:
  -- toRational
  toFloat x = realToFrac x

subtract :: Num a => a -> a -> a
subtract x y = y - x

even, odd :: Integral a => a -> Bool
even n = n `rem` 2 == 0
odd n = not (even n)

gcd, lcm :: Integral a => a -> a -> a
gcd m n
  | m == 0 && n == 0 = error "Prelude.gcd 0 0"
  | otherwise = gcd' (abs m) (abs n)
  where gcd' m n = if n == 0 then m else gcd' n (m `rem` n)
lcm m n
  | m == 0 || n == 0 = 0
  | otherwise = abs ((m `quot` gcd m n) * n)

(^) :: (Num a,Integral b) => a -> b -> a
x ^ n
  | n == 0 = 1
  | n > 0  = f x (n - 1) x
  | otherwise = error "Prelude.^: negative exponent"
  where f x n y = if n == 0 then y else g x n y
        g x n y =
          if even n then g (x * x) (n `quot` 2) y else f x (n - 1) (x * y)

(^^) :: (Fractional a,Integral b) => a -> b -> a
x ^^ n = if n >= 0 then x ^ n else 1 / x ^ (-n)

fromIntegral :: (Integral a,Num b) => a -> b
fromIntegral n = fromInteger (toInteger n)

realToFrac :: (Real a,Fractional b) => a -> b
realToFrac x = fromRational (toRational x)


-- Types of primitive arithmetic functions and predicates
data Int
instance Eq Int where
  (==) = primEqInt
    where foreign import ccall "prims.h" primEqInt :: Int -> Int -> Bool
  (/=) = primNeqInt
    where foreign import ccall "prims.h" primNeqInt :: Int -> Int -> Bool
instance Ord Int where
  (<) = primLtInt
    where foreign import ccall "prims.h" primLtInt :: Int -> Int -> Bool
  (<=) = primLeqInt
    where foreign import ccall "prims.h" primLeqInt :: Int -> Int -> Bool
  (>=) = primGeqInt
    where foreign import ccall "prims.h" primGeqInt :: Int -> Int -> Bool
  (>) = primGtInt
    where foreign import ccall "prims.h" primGtInt :: Int -> Int -> Bool
instance Enum Int where
  succ n | n < maxBound = n + 1
  pred n | n > minBound = n - 1
  toEnum n = n
  fromEnum n = n
  enumFrom n = enumFromTo n maxBound
  enumFromThen n1 n2 =
    enumFromThenTo n1 n2 (if n1 <= n2 then maxBound else minBound)
  enumFromTo n m = takeWhile (m >=) (iterate (1 +) n)
  enumFromThenTo n1 n2 m =
    takeWhile (if n1 <= n2 then (m >=) else (m <=)) (iterate (n2 - n1 +) n1)
instance Bounded Int where
  minBound = primMinInt
    where foreign import ccall "prims.h" primMinInt :: Int
  maxBound = primMaxInt
    where foreign import ccall "prims.h" primMaxInt :: Int
instance Show Int where
  -- FIXME: use a dedicated primitive for this
  showsPrec p x = showParen (p > 6 && x < 0) (shows x)
    where foreign import primitive shows :: a -> ShowS

instance Num Int where
  (+) = primAddInt
    where foreign import ccall "prims.h" primAddInt :: Int -> Int -> Int
  (-) = primSubInt
    where foreign import ccall "prims.h" primSubInt :: Int -> Int -> Int
  (*) = primMulInt
    where foreign import ccall "prims.h" primMulInt :: Int -> Int -> Int
  negate n = 0 - n
  abs n = if n >= 0 then n else - n
  signum n = if n > 0 then 1 else if n < 0 then -1 else 0
  fromInt n = n
  fromInteger = primFromInteger
    where foreign import rawcall "integer.h" primFromInteger :: Integer -> Int

instance Real Int where
  toRational n = fromInt n

instance Integral Int where
  quot = primQuotInt
    where foreign import ccall "prims.h" primQuotInt :: Int -> Int -> Int
  rem = primRemInt
    where foreign import ccall "prims.h" primRemInt :: Int -> Int -> Int
  div = primDivInt
    where foreign import ccall "prims.h" primDivInt :: Int -> Int -> Int
  mod = primModInt
    where foreign import ccall "prims.h" primModInt :: Int -> Int -> Int
  quotRem n d = (n `quot` d, n `rem` d)
  divMod n d = (n `div` d, n `mod` d)
  toInt n = n
  toInteger = primToInteger
    where foreign import rawcall "integer.h" primToInteger :: Int -> Integer


data Integer
instance Eq Integer where
  (==) = primEqInteger
    where foreign import rawcall "integer.h"
    	  	  	 primEqInteger :: Integer -> Integer -> Bool
  (/=) = primNeqInteger
    where foreign import rawcall "integer.h"
    	  	  	 primNeqInteger :: Integer -> Integer -> Bool

instance Ord Integer where
  compare = primCompareInteger
    where foreign import rawcall "integer.h"
    	  	  	 primCompareInteger :: Integer -> Integer -> Ordering
  (<) = primLtInteger
    where foreign import rawcall "integer.h"
    	  	  	 primLtInteger :: Integer -> Integer -> Bool
  (<=) = primLeqInteger
    where foreign import rawcall "integer.h"
    	  	  	 primLeqInteger :: Integer -> Integer -> Bool
  (>=) = primGeqInteger
    where foreign import rawcall "integer.h"
    	  	  	 primGeqInteger :: Integer -> Integer -> Bool
  (>) = primGtInteger
    where foreign import rawcall "integer.h"
    	  	  	 primGtInteger :: Integer -> Integer -> Bool

instance Enum Integer where
  succ = primSuccInteger
    where foreign import rawcall "integer.h"
    	  	  	 primSuccInteger :: Integer -> Integer
  pred = primPredInteger
    where foreign import rawcall "integer.h"
    	  	  	 primPredInteger :: Integer -> Integer
  toEnum n = toInteger n
  fromEnum n = fromInteger n
  enumFrom n = iterate succ n
  enumFromTo n m = takeWhile (m >=) (enumFrom n)
  enumFromThen n1 n2 = iterate (n2 - n1 +) n1
  enumFromThenTo n1 n2 m =
    takeWhile (if n1 <= n2 then (m >=) else (m <=)) (enumFromThen n1 n2)

instance Show Integer where
  -- FIXME: use a dedicated primitive for this
  showsPrec p x = showParen (p > 6 && x < 0) (shows x)
    where foreign import primitive shows :: a -> ShowS

instance Num Integer where
  (+) = primAddInteger
    where foreign import rawcall "integer.h"
    	  	  	 primAddInteger :: Integer -> Integer -> Integer
  (-) = primSubInteger
    where foreign import rawcall "integer.h"
    	  	  	 primSubInteger :: Integer -> Integer -> Integer
  (*) = primMulInteger
    where foreign import rawcall "integer.h"
    	  	  	 primMulInteger :: Integer -> Integer -> Integer
  negate = primNegateInteger
    where foreign import rawcall "integer.h"
    	  	  	 primNegateInteger :: Integer -> Integer
  abs = primAbsInteger
    where foreign import rawcall "integer.h"
    	  	  	 primAbsInteger :: Integer -> Integer
  signum = primSignumInteger
    where foreign import rawcall "integer.h"
    	  	  	 primSignumInteger :: Integer -> Integer
  fromInt n = toEnum n
  fromInteger n = n

instance Real Integer where
  toRational n = fromInteger n

instance Integral Integer where
  quot = primQuotInteger
    where foreign import rawcall "integer.h"
    	  	  	 primQuotInteger :: Integer -> Integer -> Integer
  rem = primRemInteger
    where foreign import rawcall "integer.h"
    	  	  	 primRemInteger :: Integer -> Integer -> Integer
  div = primDivInteger
    where foreign import rawcall "integer.h"
    	  	  	 primDivInteger :: Integer -> Integer -> Integer
  mod = primModInteger
    where foreign import rawcall "integer.h"
    	  	  	 primModInteger :: Integer -> Integer -> Integer
  quotRem = primQuotRemInteger
    where foreign import rawcall "integer.h"
    	  	  	 primQuotRemInteger :: Integer -> Integer -> (Integer,Integer)
  divMod = primDivModInteger
    where foreign import rawcall "integer.h"
    	  	  	 primDivModInteger :: Integer -> Integer -> (Integer,Integer)
  toInt n = fromEnum n
  toInteger n = n


data Float
instance Eq Float where
  (==) = primEqFloat
    where foreign import ccall "prims.h" primEqFloat :: Float -> Float -> Bool
  (/=) = primNeqFloat
    where foreign import ccall "prims.h" primNeqFloat :: Float -> Float -> Bool
instance Ord Float where
  (<) = primLtFloat
    where foreign import ccall "prims.h" primLtFloat :: Float -> Float -> Bool
  (<=) = primLeqFloat
    where foreign import ccall "prims.h" primLeqFloat :: Float -> Float -> Bool
  (>=) = primGeqFloat
    where foreign import ccall "prims.h" primGeqFloat :: Float -> Float -> Bool
  (>) = primGtFloat
    where foreign import ccall "prims.h" primGtFloat :: Float -> Float -> Bool
  -- The following implementation of compare is designed such that compare
  -- has no solution if one of the arguments is NaN.
  x `compare` y
    | x < y = LT
    | x > y = GT
    | x == y = EQ
instance Enum Float where
  -- NB This is a rather dubious instance; it is defined just for
  --    compatibility with the Haskell report
  succ x = x + 1
  pred x = x - 1
  toEnum n = fromInt n
  fromEnum x = truncate x
  enumFrom x = iterate (1 +) x
  enumFromTo x1 x2 = takeWhile (<= x2 + 0.5) (enumFrom x1)
  enumFromThen x1 x2 = [x1 + n * i | n <- enumFrom 0]
    where i = x2 - x1
  enumFromThenTo x1 x2 x3 =
    takeWhile (if x1 <= x2 then (<= lim) else (>= lim)) (enumFromThen x1 x2)
    where lim = x3 + (x2 - x1) * 0.5
instance Show Float where
  -- FIXME: use a dedicated primitive for this
  -- FIXME: check for negative zeros, too
  showsPrec p x = showParen (p > 6 && x < 0) (shows x)
    where foreign import primitive shows :: a -> ShowS

instance Num Float where
  (+) = primAddFloat
    where foreign import ccall "prims.h" primAddFloat :: Float -> Float -> Float
  (-) = primSubFloat
    where foreign import ccall "prims.h" primSubFloat :: Float -> Float -> Float
  (*) = primMulFloat
    where foreign import ccall "prims.h" primMulFloat :: Float -> Float -> Float
  negate x = 0 - x
  abs x =
    -- NB this implementation ensures that abs of a negative zero is positive
    if x <= 0 then - x else x
  signum x =
    -- NB use compare so that signum NaN has no solution
    case x `compare` 0 of
      LT -> -1
      EQ -> 0
      GT -> 1
  fromInt = primFloat
    where foreign import ccall "prims.h" primFloat  :: Int -> Float
  fromInteger = primIntegerToFloat
    where foreign import rawcall "integer.h"
    	  	  	 primIntegerToFloat :: Integer -> Float

instance Real Float where
  toRational = primFloatToRational
    where foreign import rawcall "integer.h"
    	  	  	 primFloatToRational :: Float -> Rational

instance Fractional Float where
  (/) = primDivFloat
    where foreign import ccall "prims.h" primDivFloat :: Float -> Float -> Float
  fromRational x = fromInteger (numerator x) / fromInteger (denominator x)
  fromFloat x = x

instance RealFrac Float where
  properFraction x =
    case primProperFraction x of
      (n,y) -> (fromInteger n,y)
    where foreign import rawcall "integer.h"
    	  	  	 primProperFraction :: Float -> (Integer,Float)

instance Floating Float where
  pi = 3.14159265358979323846
  exp = exp where foreign import ccall "math.h" exp :: Float -> Float
  log = log where foreign import ccall "math.h" log :: Float -> Float
  sqrt = sqrt where foreign import ccall "math.h" sqrt :: Float -> Float
  (**) = pow where foreign import ccall "math.h" pow :: Float -> Float -> Float
  sin = sin where foreign import ccall "math.h" sin :: Float -> Float
  cos = cos where foreign import ccall "math.h" cos :: Float -> Float
  tan = tan where foreign import ccall "math.h" tan :: Float -> Float
  asin = asin where foreign import ccall "math.h" asin :: Float -> Float
  acos = acos where foreign import ccall "math.h" acos :: Float -> Float
  atan = atan where foreign import ccall "math.h" atan :: Float -> Float
  sinh = sinh where foreign import ccall "math.h" sinh :: Float -> Float
  cosh = cosh where foreign import ccall "math.h" cosh :: Float -> Float
  tanh = tanh where foreign import ccall "math.h" tanh :: Float -> Float
  asinh = asinh where foreign import ccall "math.h" asinh :: Float -> Float
  acosh = acosh where foreign import ccall "math.h" acosh :: Float -> Float
  atanh = atanh where foreign import ccall "math.h" atanh :: Float -> Float

instance RealFloat Float where
  atan2 = atan2
    where foreign import ccall "math.h" atan2 :: Float -> Float -> Float
  toFloat x = x
  

-- Constraints
-- NB The Success constructor is not exported from the Prelude, but the
--    compiler knows about it
data Success = Success
instance Show Success where
  show c | c = "success"

--- Equational constraint
foreign import primitive (=:=) :: a -> a -> Success

--- Disequality constraint
foreign import primitive (=/=) :: a -> a -> Success

--- Lazy unification (for function patterns only)
-- To do: This should not be exported from the Prelude, but from module Unsafe
foreign import primitive (=:<=) :: a -> a -> Success

--- Always satisfiable constraint
success :: Success
success = Success

--- Concurrent conjunction of constraints
foreign import primitive (&) :: Success -> Success -> Success

--- Guarded evaluation
(&>) :: Success -> a -> a
c &> e = case c of Success -> e


-- Maybe type

data Maybe a = Nothing | Just a deriving (Eq,Ord,Show)
instance Functor Maybe where
  fmap f (Just x) = Just (f x)
  fmap _ Nothing = Nothing
instance Monad Maybe where
  return x      = Just x
  Just x  >>= f = f x
  Nothing >>= _ = Nothing
  Just _  >> y	= y
  Nothing >> _	= Nothing
  fail _     	= Nothing

maybe		   :: b -> (a -> b) -> Maybe a -> b
maybe z _ Nothing  = z
maybe _ f (Just x) = f x


-- Either type

data Either a b = Left a | Right b deriving (Eq,Ord,Show)

either		     :: (a -> c) -> (b -> c) -> Either a b -> c
either f _ (Left x)  = f x
either _ g (Right y) = g y


-- Monadic IO

data IO a  -- conceptually: World -> (a,World)
instance Functor IO where
  fmap f x = x >>= \y -> return (f y)
instance Monad IO where
  return = primReturn
    where foreign import primitive "return" primReturn :: a -> IO a
  (>>=) = primBind
    where foreign import primitive ">>=" primBind :: IO a -> (a -> IO b) -> IO b
  (>>) = primBind_
    where foreign import primitive ">>" primBind_ :: IO a -> IO b -> IO b
  fail s = ioError s

type FilePath = String

--- The empty action that returns nothing.
done :: Monad m => m ()
done = return ()

--- Action that (lazily) reads file and returns its contents.
readFile :: FilePath -> IO String
readFile fn = openFile fn ReadMode >>= hGetContents

--- Actions that writes a file.
writeFile :: FilePath -> String -> IO ()
writeFile fn str = bracket (openFile fn WriteMode) hClose (flip hPutStr str)

--- Actions that appends a string to a file.
appendFile :: FilePath -> String -> IO ()
appendFile fn str = bracket (openFile fn AppendMode) hClose (flip hPutStr str)

--- Action to read a single character from stanard input.
getChar :: IO Char
getChar = hGetChar stdin

--- Action to read a single line from standard input.
getLine :: IO String
getLine = hGetLine stdin

--- Action that (lazily) reads all of standard input.
getContents :: IO String
getContents = hGetContents stdin

--- Action to print a character on stdout.
putChar :: Char -> IO ()
putChar = hPutChar stdout

--- Action to print a string on stdout.
putStr :: String -> IO ()
putStr = hPutStr stdout
 
--- Action to print a string with a newline on stdout.
putStrLn :: String -> IO ()
putStrLn = hPutStrLn stdout

--- Converts a term into a string and prints it.
print   :: Show a => a -> IO ()
print t = putStrLn (show t)

--- Convert a simple stream filter into an I/O program
--- Note: interact closes the standard input
interact   :: (String -> String) -> IO ()
interact f = getContents >>= putStr . f

--- Solves a constraint as an I/O action.
--- Note: the constraint should be always solvable in a deterministic way
doSolve :: Success -> IO ()
doSolve constraint | constraint = done


-- Auxiliary monad functions

--- Execute a sequence of actions and collect all results in a list
sequence :: Monad m => [m a] -> m [a]
sequence = foldr mcons (return [])
  where mcons m ms = do x <- m; xs <- ms; return (x:xs)

--- Execute a sequence of actions and ignore the result
sequence_ :: Monad m => [m a] -> m ()
sequence_ = foldr (>>) done

--- Map an action function on a list of elements.
--- The results are of all I/O actions are collected in a list.
mapM :: Monad m => (a -> m b) -> [a] -> m [b]
mapM f ms = sequence (map f ms)

--- Map an action function on a list of elements.
--- The results are of all I/O actions are ignored.
mapM_ :: Monad m => (a -> m b) -> [a] -> m ()
mapM_ f ms = sequence_ (map f ms)

-- NB sequenceIO, sequenceIO_, mapIO, map_IO currently retained for
--    backward compatibility
sequenceIO :: [IO a] -> IO [a]
sequenceIO = sequence

sequenceIO_ :: [IO a] -> IO ()
sequenceIO_ = sequence_

mapIO :: (a -> IO b) -> [a] -> IO [b]
mapIO = mapM

mapIO_ :: (a -> IO b) -> [a] -> IO ()
mapIO_ = mapM_


-- IO Exceptions
-- At present exception values are strings, this will change in the future
type IOError = String

--- Raise an I/O exception
foreign import primitive ioError :: IOError -> IO a

--- Establish an exception handler for the execution of an action
foreign import primitive catch :: IO a -> (IOError -> IO a) -> IO a


----------------------------------------------------------------
-- Encapsulated search:

--- Basic search control operator.
foreign import primitive try :: (a -> Success) -> [a -> Success]


--- Non-deterministic choice par excellence
(?)   :: a -> a -> a
x ? _ = x
_ ? y = y


--- Evaluates to a fresh free variable.
unknown :: a
unknown = x where x free


--- Inject operator which adds the application of the unary
--- procedure p to the search variable to the search goal
--- taken from Oz. p x comes before g x to enable a test+generate
--- form in a sequential implementation.
inject	   :: (a -> Success) -> (a -> Success) -> (a -> Success) 
inject g p = \x -> p x & g x

--- Compute all solutions via a left-to-right strategy.
solveAll   :: (a -> Success) -> [a -> Success]
solveAll g = all (try g) []
  where all []           gs  = all2 gs
        all [g]          gs  = g : all2 gs 
        all (g:gs@(_:_)) gs' = all (try g) (gs ++ gs')

        all2 []     = []
        all2 (g:gs) = all (try g) gs


--- Get the first solution via left-to-right strategy.
once :: (a -> Success) -> a -> Success
once g = head (solveAll g)


--- Get the best solution via left-to-right strategy according to
--- a specified operator that can always take a decision which
--- of two solutions is better.
--- In general, the comparison operation should be rigid in its arguments!
best    :: (a -> Success) -> (a -> a -> Bool) -> [a -> Success]
best g compare = bestHelp [] (try g) []
 where
   bestHelp [] []     curbest = curbest
   bestHelp [] (y:ys) curbest = evalB (try (constrain y curbest)) ys curbest
   bestHelp (x:xs) ys curbest = evalA (try x) xs ys curbest
   
   evalB []         ys curbest = bestHelp [] ys curbest
   evalB [newbest]  ys _       = bestHelp [] ys [newbest]
   evalB (x1:x2:xs) ys curbest = bestHelp (x1:x2:xs) ys curbest
   
   evalA []         xs ys curbest = bestHelp xs ys curbest
   evalA [newbest]  xs ys _       = bestHelp [] (xs++ys) [newbest]
   evalA (u1:u2:us) xs ys curbest = bestHelp ((u1:u2:us)++xs) ys curbest
   
   constrain b []        = b
   constrain b [curbest] =
       inject b (\x -> let y free in curbest y & compare x y =:= True)


--- Get all solutions via left-to-right strategy and unpack
--- the values from the lambda-abstractions.
--- Similar to Prolog's findall.
findall :: (a -> Success) -> [a]
findall g = map unpack (solveAll g)

--- Get the first solution via left-to-right strategy
--- and unpack the values from the search goals.
findfirst :: (a -> Success) -> a
findfirst g = head (findall g)


--- Show the solution of a solved constraint.
browse  :: Show a => (a -> Success) -> IO ()
browse g = putStr (show (unpack g))

--- Unpack solutions from a list of lambda abstractions and write 
--- them to the screen.
browseList :: Show a => [a -> Success] -> IO ()
browseList [] = done
browseList (g:gs) = browse g >> putChar '\n' >> browseList gs


--- Unpack a solution's value from a (solved) search goal.
unpack  :: (a -> Success) -> a
unpack g | g x  = x  where x free
