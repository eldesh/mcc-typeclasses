-- Check that type synoyms can have higher kinds

type List = []

data T f a = T (f a)

lmap :: (a -> b) -> T List a -> T List b
lmap f (T xs) = T (map f xs)
