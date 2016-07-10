module tc003 where

-- the following definitions are not yet in the Prelude
show :: Show a => a -> String
show = undefined

class Read a where
read :: Read a => String -> a
read = undefined

-- checks that an ambiguous type in the rhs of a pattern declaration
-- is reported
f x = y
  where (y,z) = (\(c:cs) -> (c,cs)) $ tc003.show (read x)
