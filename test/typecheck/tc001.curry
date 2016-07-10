module tc001 where

-- the following definitions are not yet in the Prelude
show :: Show a => a -> String
show = undefined

class Read a where
read :: Read a => String -> a
read = undefined

cast = tc001.read . tc001.show
