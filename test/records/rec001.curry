-- A simple test ensuring that records declarations are accepted (see
-- also rec002.curry, rec003.curry, and rec004.curry for variants of this
-- example)

module rec001 where
data Item = File{ name :: String }
     	  | Directory { name :: String, contents::[Item] }
	  | Link{ name, original :: String }

count :: Item -> Int
count (File _) = 1
count (Directory _ contents) = foldr ((+) . count) 1 contents
count (Link _ _) = 0

infix 4 :=
data Assoc a b = (:=){ key :: a, val :: b }

lookup x = foldr (match x) Nothing
  where match x (y:=z) = if x==y then const (Just z) else id

trans c = rec001.lookup c [base+1:='a',base+2:='b',base+3:='c']
  where base = ord '@'

newtype Identity a = Id{ unId :: a }

identity (Id x) = Id x
