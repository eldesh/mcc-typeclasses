-- A simple example checking the dictionary transformation when type
-- variables with higher kinds are involved. The function f below is
-- borrowed from Sect. 4.5.3 of the Haskell report.

--f :: (Monad m, Eq (m a)) => a -> m a -> Bool
f x y = return x == y

-- Functions g and h are specializations of f with respect to the monad
-- and the argument variable, respectively.
--g :: Eq a => a -> Bool
g x = f x []

--h :: (Monad m, Eq (m Int)) => m Int -> Bool
h y = f (0::Int) y

-- The main function checks all three functions at different
-- types and should succeed.
main = foldr (&>) success [
    f () (Just ()) =:= True,
    f 1.0 [1,2,3] =:= False,
    g () =:= False,
    g "" =:= False,
    h (Just 0) =:= True,
    h [] =:= False
  ]
