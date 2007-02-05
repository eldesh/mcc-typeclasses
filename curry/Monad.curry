module Monad(module Monad,
       	     {- re-exported Prelude entitites -}
	     Monad((>>=), (>>), return, fail),
             Functor(fmap),
	     mapM, mapM_, sequence, sequence_{-, (=<<)-}) where

infixr 1 =<<

{- functions from Haskell's Prelude -}
(=<<) :: Monad m => (a -> m b) -> m a -> m b
f =<< m = m >>= f


{- functions from the Monad module -}
class Monad m => MonadPlus m where
  mzero :: m a
  mplus :: m a -> m a -> m a

instance MonadPlus Maybe where
  mzero	 	    = Nothing
  Nothing `mplus` y = y
  Just x  `mplus` _ = Just x

instance MonadPlus [] where
  mzero = []
  mplus = (++)


join :: Monad m => m (m a) -> m a
join m = m >>= id

guard :: MonadPlus m => Bool -> m ()
guard True = done
guard False = mzero

when :: Monad m => Bool -> m () -> m ()
when True m = m
when False m = done

unless :: Monad m => Bool -> m () -> m ()
unless b = when (not b)

ap :: Monad m => m (a -> b) -> m a -> m b
ap = liftM2 ($)


mapAndUnzipM :: Monad m => (a -> m (b,c)) -> [a] -> m ([b],[c])
mapAndUnzipM f xs = liftM unzip (mapM f xs)

zipWithM :: Monad m => (a -> b -> m c) -> [a] -> [b] -> m [c]
zipWithM f xs ys = sequence (zipWith f xs ys)

zipWithM_ :: Monad m => (a -> b -> m c) -> [a] -> [b] -> m ()
zipWithM_ f xs ys = sequence_ (zipWith f xs ys)

foldM :: Monad m => (a -> b -> m a) -> a -> [b] -> m a
foldM f z [] = return z
foldM f z (x:xs) = do y <- f z x; foldM f y xs

filterM :: Monad m => (a -> m Bool) -> [a] -> m [a]
filterM f [] = return []
filterM f (x:xs) =
  do b <- f x
     if b then do xs' <- filterM f xs; return (x:xs')
          else filterM f xs

msum :: MonadPlus m => [m a] -> m a
msum = foldr mplus mzero


liftM :: Monad m => (a -> b) -> (m a -> m b)
liftM f m = do x <- m; return (f x)

liftM2 :: Monad m => (a -> b -> c) -> (m a -> m b -> m c)
liftM2 f m1 m2 = do x <- m1; y <- m2; return (f x y)

liftM3 :: Monad m => (a -> b -> c -> d) -> (m a -> m b -> m c -> m d)
liftM3 f m1 m2 m3 = do x <- m1; y <- m2; z <- m3; return (f x y z)

liftM4 :: Monad m => (a -> b -> c -> d -> e)
       -> (m a -> m b -> m c -> m d -> m e)
liftM4 f m1 m2 m3 m4 =
   do w <- m1; x <- m2; y <- m3; z <- m4
      return (f w x y z)

liftM5 :: Monad m => (a -> b -> c -> d -> e -> f)
       -> (m a -> m b -> m c -> m d -> m e -> m f)
liftM5 f m1 m2 m3 m4 m5 =
  do v <- m1; w <- m2; x <- m3; y <- m4; z <- m5
     return (f v w x y z)


