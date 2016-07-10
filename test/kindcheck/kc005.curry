-- This checks that arrow instances are handled correctly

class FUNCTOR f where
  f_map :: (a -> b) -> f a -> f b

instance FUNCTOR ((->) c) where
  --f_map :: (a -> b) -> (c -> a) -> (c -> b)
  f_map f g = f . g

f = f_map sqr twice
sqr x = x * x
twice x = x + x

main = print (f 5)
