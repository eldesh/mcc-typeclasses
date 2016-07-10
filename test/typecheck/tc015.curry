f :: (Show a, Show a) => a -> String
f x | x == x = show x
