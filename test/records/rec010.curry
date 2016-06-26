-- This test checks that record field labels -- in contrast to the
-- corresponding selector functions -- are not shadowed by local
-- variables.

infix 4 :=

data Assoc a b = (:=){ key::a, val::b }

nubKeys :: Eq a => [Assoc a b] -> [Assoc a b]
nubKeys [] = []
nubKeys ((key:=val) : rest) =
  (:=){ key=key, val=val } : filter (not . sameKey key) (nubKeys rest)
  where sameKey key (:=){ key=key' } = key==key'

nubVals :: Eq b => [Assoc a b] -> [Assoc a b]
nubVals [] = []
nubVals ((key:=val) : rest) =
  (:=){ val=val, key=key } : filter (not . sameVal val) (nubVals rest)
  where sameVal val (:=){ val=val' } = val==val'
