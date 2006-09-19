module Monad(module Monad,
       	     {- re-exported Prelude entitites -}
	     (>>=), (>>), return) where

infixr 1 =<<

{- functions from Haskell's Prelude -}
fail :: String -> IO a
fail = ioError

sequence :: [IO a] -> IO [a]
sequence = Prelude.sequenceIO

sequence_ :: [IO a] -> IO ()
sequence_ = Prelude.sequenceIO_

mapM :: (a -> IO b) -> [a] -> IO [b]
mapM = Prelude.mapIO

mapM_ :: (a -> IO b) -> [a] -> IO ()
mapM_ = Prelude.mapIO_

(=<<) :: (a -> IO b) -> IO a -> IO b
f =<< m = m >>= f

fmap :: (a -> b) -> IO a -> IO b
fmap = liftM

{- functions from the Monad module -}
join :: IO (IO a) -> IO a
join m = m >>= id

when :: Bool -> IO () -> IO ()
when True m = m
when False m = done

unless :: Bool -> IO () -> IO ()
unless b = when (not b)

ap :: IO (a -> b) -> IO a -> IO b
ap = liftM2 ($)


mapAndUnzipM :: (a -> IO (b,c)) -> [a] -> IO ([b],[c])
mapAndUnzipM f xs = liftM unzip (mapM f xs)

zipWithM :: (a -> b -> IO c) -> [a] -> [b] -> IO [c]
zipWithM f xs ys = sequence (zipWith f xs ys)

zipWithM_ :: (a -> b -> IO c) -> [a] -> [b] -> IO ()
zipWithM_ f xs ys = sequence_ (zipWith f xs ys)

foldM :: (a -> b -> IO a) -> a -> [b] -> IO a
foldM f z [] = return z
foldM f z (x:xs) = do y <- f z x; foldM f y xs

filterM :: (a -> IO Bool) -> [a] -> IO [a]
filterM f [] = return []
filterM f (x:xs) =
  do b <- f x
     if b then do xs' <- filterM f xs; return (x:xs')
          else filterM f xs


liftM :: (a -> b) -> (IO a -> IO b)
liftM f m = do x <- m; return (f x)

liftM2 :: (a -> b -> c) -> (IO a -> IO b -> IO c)
liftM2 f m1 m2 = do x <- m1; y <- m2; return (f x y)

liftM3 :: (a -> b -> c -> d) -> (IO a -> IO b -> IO c -> IO d)
liftM3 f m1 m2 m3 = do x <- m1; y <- m2; z <- m3; return (f x y z)

liftM4 :: (a -> b -> c -> d -> e) -> (IO a -> IO b -> IO c -> IO d -> IO e)
liftM4 f m1 m2 m3 m4 =
   do w <- m1; x <- m2; y <- m3; z <- m4
      return (f w x y z)

liftM5 :: (a -> b -> c -> d -> e -> f)
       -> (IO a -> IO b -> IO c -> IO d -> IO e -> IO f)
liftM5 f m1 m2 m3 m4 m5 =
  do v <- m1; w <- m2; x <- m3; y <- m4; z <- m5
     return (f v w x y z)


