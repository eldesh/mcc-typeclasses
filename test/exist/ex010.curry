-- Here is a rather contrived example combining universal and exisential
-- quantification with constraints. Note that the Functor constraint on
-- T is not stricly necessary (in fact, any constraint on universally
-- quantified variables in a data type declaration is not necessary).

data Functor f => T f = forall a. (Enum a, Show (f a)) => T (f a)

instance Functor f => Show (T f) where
  showsPrec p (T xs) = showsPrec p xs

tenum :: Functor f => T f -> f Int
tenum (T xs) = fmap fromEnum xs

main =
  do
    let ts = [T [1,2,3], T "hello"]
    putStrLn (show ts ++ " => " ++ show (map tenum ts))
    let t' = T (Just ())
    putStrLn (show t' ++ " => " ++ show (tenum t'))
