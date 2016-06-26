-- A simple test ensuring that records patterns and expressions work (see
-- also rec001.curry, rec003.curry, and rec004.curry for variants of this
-- example)

data Item = File{ name :: String }
     	  | Directory { name :: String, contents::[Item] }
	  | Link{ name, original :: String }

count :: Item -> Int
count File{} = 1
count Directory{ contents=contents } = foldr ((+) . count) 1 contents
count Link{} = 0

infix 4 :=
data Assoc a b = (:=){ key :: a, val :: b }

lookupAssoc x = foldr (match x) Nothing
  where match x (:=){ val=z, key=y } = if x==y then const (Just z) else id

trans c = lookupAssoc c [(:=){ val='a', key=base+1 },
                         (:=){ val='b', key=base+2 },
		         (:=){ val='c', key=base+3 }]
  where base = ord '@'

newtype Identity a = Id{ unId :: a }

identity Id{ unId = x } = Id{ unId = x }
