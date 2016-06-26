module A where
newtype Pair a b = Pair (a,b)
mkPair x y = Pair (x,y)
left (Pair (x,_)) = x
right (Pair (_,y)) = y
