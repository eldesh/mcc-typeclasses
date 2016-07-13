-- A minimal Prelude
module Prelude where
infixr 5 :,++
infix  4 =:=
infixr 3 &&
infixr 2 ||
infixr 0 &, &>

data () = ()
data (,) a b = (,) a b
data (,,) a b c = (,,) a b c
data [] a = [] | a : [a]
data Bool = False | True
data IO a

(.) :: (b -> c) -> (a -> b) -> (a -> c)
(f . g) x = f (g x)

flip f x y = f y x
curry f (x,y) = f x y
uncurry f x y = f (x,y)

not False = True
not True = False

False && _ = False
True && x = x

False || x = x
True || _ = True

head (x:_) = x
tail (_:xs) = xs

[] ++ ys = ys
(x:xs) ++ ys = x : xs ++ ys

map f [] = []
map f (x:xs) = f x : map f xs

foldr f z [] = z
foldr f z (x:xs) = f x (foldr f z xs)

foldl f z [] = z
foldl f z (x:xs) = foldl f (f z x) xs

concat = foldr (++) []
concatMap f = concat . map f

foreign import primitive (&) :: Bool -> Bool -> Bool
foreign import primitive (=:=) :: a -> a -> Bool
c &> e | c = e

foreign import primitive return :: a -> IO a
doSolve c | c = return ()
