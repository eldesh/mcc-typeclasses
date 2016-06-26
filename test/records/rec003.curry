-- A simple test ensuring that selector functions for records work (see
-- also rec001.curry, rec002.curry, and rec004.curry for variants of this
-- example)

data Item = File{ name :: String }
     	  | Directory { name :: String, contents::[Item] }
	  | Link{ name, original :: String }

count :: Item -> Int
count (File _) = 1
count item@(Directory _ _) = foldr ((+) . count) 1 (contents item)
count (Link _ _) = 0

infix 4 :=
data Assoc a b = (:=){ key :: a, val :: b }

lookup x = foldr (match x) Nothing
  where match x y = if x == key y then const (Just (val y)) else id

newtype Identity a = Id{ unId :: a }

identity i = Id (unId i)
