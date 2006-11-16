-- finite maps based on 2-3 trees

-- Copyright (c) 1999-2006, Wolfgang Lux
-- See ../LICENSE for the full license.

module FiniteMap(FM, nullFM, zeroFM, unitFM, addToFM, deleteFromFM,
                 lookupFM, fromListFM, toListFM,
                 showFM, showsFM, mapFM) where

data FM a b =
    Empty
  | Node2 (FM a b) (a,b) (FM a b)
  | Node3 (FM a b) (a,b) (FM a b) (a,b) (FM a b)

instance (Eq a, Eq b) => Eq (FM a b) where
  xys1 == xys2 = toListFM xys1 == toListFM xys2

nullFM :: FM a b -> Bool
nullFM Empty             = True
nullFM (Node2 _ _ _)     = False
nullFM (Node3 _ _ _ _ _) = False

zeroFM :: FM a b
zeroFM = Empty

unitFM :: a -> b -> FM a b
unitFM x y = Node2 Empty (x,y) Empty

addToFM :: a -> b -> FM a b -> FM a b
addToFM x y xys =
  case insertNode x y xys of
    Left xys' -> xys'
    Right (l,x,r) -> Node2 l x r

fromListFM :: [(a,b)] -> FM a b
fromListFM = foldr (uncurry addToFM) zeroFM

insertNode :: a -> b -> FM a b
           -> Either (FM a b) ((FM a b),(a,b),(FM a b))
insertNode k x Empty = Right (Empty,(k,x),Empty)
insertNode k x (Node2 a y b) = Left (insertNode2 k x a y b)
  where insertNode2 k x a y b =
          case compareKey k y of
     	    LT -> balanceL (insertNode k x a) y b
     	    EQ -> Node2 a (k,x) b
     	    GT -> balanceR a y (insertNode k x b)
        balanceL (Left a) x b = Node2 a x b
        balanceL (Right (a,x,b)) y c = Node3 a x b y c
        balanceR a x (Left b) = Node2 a x b
        balanceR a x (Right (b,y,c)) = Node3 a x b y c
insertNode k x (Node3 a y b z c) =
  case compareKey k y of
    LT -> balanceL (insertNode k x a) y b z c
    EQ -> Left (Node3 a (k,x) b z c)
    GT ->
      case compareKey k z of
        LT -> balanceM a y (insertNode k x b) z c
        EQ -> Left (Node3 a y b (k,x) c)
        GT -> balanceR a y b z (insertNode k x c)
  where balanceL (Left a) x b y c = Left (Node3 a x b y c)
        balanceL (Right (a,x,b)) y c z d = Right (Node2 a x b,y,Node2 c z d)
        balanceM a x (Left b) y c = Left (Node3 a x b y c)
        balanceM a x (Right (b,y,c)) z d = Right (Node2 a x b,y,Node2 c z d)
        balanceR a x b y (Left c) = Left (Node3 a x b y c)
        balanceR a x b y (Right (c,z,d)) = Right (Node2 a x b,y,Node2 c z d)

compareKey :: a -> (a,b) -> Ordering
compareKey k1 (k2,_) = compare k1 k2

deleteFromFM :: a -> FM a b -> FM a b
deleteFromFM x xys = snd (deleteNode x xys)

deleteNode :: a -> FM a b -> (Bool,FM a b)
deleteNode _ Empty = (False,Empty)
deleteNode x (Node2 a y b) =
  case compareKey x y of
    LT -> balanceL (deleteNode x a) y b
    EQ
      | nullFM a -> (True,b)
      | otherwise -> let u = findMin b in balanceR a u (deleteNode (fst u) b)
    GT -> balanceR a y (deleteNode x b)
  where balanceL (False,a) x b = (False,Node2 a x b)
        balanceL (True,a) x (Node2 b y c) = (True,Node3 a x b y c)
        balanceL (True,a) x (Node3 b y c z d) =
          (False,Node2 (Node2 a x b) y (Node2 c z d))
        balanceR a x (False,b) = (False,Node2 a x b)
        balanceR (Node2 a x b) y (True,c) = (True,Node3 a x b y c)
        balanceR (Node3 a x b y c) z (True,d) =
          (False,Node2 (Node2 a x b) y (Node2 c z d))
deleteNode x (Node3 a y b z c) = (False,deleteNode3 x a y b z c)
  where deleteNode3 x a y b z c =
    	  case compareKey x y of
    	   LT -> balanceL (deleteNode x a) y b z c
    	   EQ
    	     | nullFM a -> Node2 b z c
    	     | otherwise -> let u = findMin b in
	       		    balanceM a u (deleteNode (fst u) b) z c
    	   GT ->
    	     case compareKey x z of
    	       LT -> balanceM a y (deleteNode x b) z c
    	       EQ
    	         | nullFM c -> Node2 a y b
    	         | otherwise -> let u = findMin c in
		   	        balanceR a y b u (deleteNode (fst u) c)
    	       GT -> balanceR a y b z (deleteNode x c)
        balanceL (False,a) x b y c = Node3 a x b y c
        balanceL (True,a) x (Node2 b y c) z d = Node2 (Node3 a x b y c) z d
        balanceL (True,a) w (Node3 b x c y d) z e =
          Node3 (Node2 a w b) x (Node2 c y d) z e
        balanceM a x (False,b) y c = Node3 a x b y c
        balanceM a x (True,b) y (Node2 c z d) = Node2 a x (Node3 b y c z d)
        balanceM a w (True,b) x (Node3 c y d z e) =
          Node3 a w (Node2 b x c) y (Node2 d z e)
        balanceR a x b y (False,c) = Node3 a x b y c
        balanceR a x (Node2 b y c) z (True,d) = Node2 a x (Node3 b y c z d)
        balanceR a w (Node3 b x c y d) z (True,e) =
          Node3 a w (Node2 b x c) y (Node2 d z e)

findMin :: FM a b -> (a,b)
findMin (Node2 a x _)
  | nullFM a = x
  | otherwise = findMin a
findMin (Node3 a x _ _ _)
  | nullFM a = x
  | otherwise = findMin a

lookupFM :: a -> FM a b -> Maybe b
lookupFM _ Empty = Nothing
lookupFM x (Node2 a y b) =
  case compareKey x y of
    LT -> lookupFM x a
    EQ -> Just (snd y)
    GT -> lookupFM x b
lookupFM x (Node3 a y b z c) =
  case compareKey x y of
    LT -> lookupFM x a
    EQ -> Just (snd y)
    GT -> lookupFM x (Node2 b z c)

toListFM :: FM a b -> [(a,b)]
toListFM = flip elems []
  where elems Empty xs = xs
        elems (Node2 a x b) xs = elems a (x : elems b xs)
        elems (Node3 a x b y c) xs = elems a (x : elems b (y : elems c xs))

showFM :: FM a b -> String
showFM xys = showsFM xys ""

showsFM :: FM a b -> ShowS
showsFM xys =
  case toListFM xys of
    [] -> showString "{}"
    (xy:xys) -> showChar '{' . showp xy . showl xys
      where showl [] = showChar '}'
            showl (xy:xys) = showChar ',' . showp xy . showl xys
            showp (x,y) = shows x . showString "|->" . shows y

mapFM :: (b -> c) -> FM a b -> FM a c
mapFM f Empty = Empty
mapFM f (Node2 a (k,x) b) = Node2 (mapFM f a) (k,f x) (mapFM f b)
mapFM f (Node3 a (k,x) b (l,y) c) =
    Node3 (mapFM f a) (k,f x) (mapFM f b) (l,f y) (mapFM f c)

{-
checkTree :: FM a b -> Int
checkTree Empty = 0
checkTree (Node2 a _ b)
  | h == checkTree b = h + 1
  | otherwise = error "checkTree: unbalanced 2-3 tree"
  where h = checkTree a
checkTree (Node3 a _ b _ c)
  | h == checkTree b && h == checkTree c = h + 1
  | otherwise = error "checkTree: unbalanced 2-3 tree"
  where h = checkTree a
-}
