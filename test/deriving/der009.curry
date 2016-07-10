-- Test that deriving an Enum instance works even for a data type with
-- only a single (constant) constructor. In particular, the pred and succ
-- instance methods must be equivalent to Prelude.failed.

data T = T deriving (Bounded,Enum,Show)

main =
  do
    print (findall (\x -> x=:=pred T))
    print (findall (\x -> x=:=succ T))
    print ([minBound .. maxBound] :: [T])
