module tc022 where

-- Ambiguous type inside an explicitly typed expression
show :: Show a => a -> String
show = undefined

class Read a where
read :: Read a => String -> a
read = undefined

f x = tc022.show (read x) :: String
