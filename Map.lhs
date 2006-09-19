% -*- LaTeX -*-
% $Id: Map.lhs 1744 2005-08-23 16:17:12Z wlux $
%
% Copyright (c) 1999-2002, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Map.lhs}
\section{Maps}
The module \texttt{Map} implements finite maps using 2-3 trees.
\begin{verbatim}

> module Map(FM, nullFM, zeroFM, unitFM, addToFM, deleteFromFM,
>            lookupFM, fromListFM, toListFM) where
> import List

\end{verbatim}
A 2-3 tree is either empty or a node with either two or three children
that are themselves 2-3 trees of the same height. Thus, a 2-3 is
always balanced.
\begin{verbatim}

> data FM a b =
>     Empty
>   | Node2 (FM a b) (a,b) (FM a b)
>   | Node3 (FM a b) (a,b) (FM a b) (a,b) (FM a b)

> nullFM :: Ord a => FM a b -> Bool
> nullFM Empty = True
> nullFM _ = False

> zeroFM :: Ord a => FM a b
> zeroFM = Empty

> unitFM :: Ord a => a -> b -> FM a b
> unitFM x y = Node2 Empty (x,y) Empty

\end{verbatim}
Insertion into the map is performed with the help of an auxiliary
function. This function returns either the updated node or a triple of
a left and right subtree together with the element between them
if the height of the tree must be changed.
\begin{verbatim}

> addToFM :: Ord a => a -> b -> FM a b -> FM a b
> addToFM x y xys =
>   case insertNode x y xys of
>     Left xys' -> xys'
>     Right (l,x,r) -> Node2 l x r

> fromListFM :: Ord a => [(a,b)] -> FM a b
> fromListFM = foldr (uncurry addToFM) zeroFM

> insertNode :: Ord a => a -> b -> FM a b
>            -> Either (FM a b) ((FM a b),(a,b),(FM a b))
> insertNode k x Empty = Right (Empty,(k,x),Empty)
> insertNode k x (Node2 a y b) =
>   Left (case compareKey k y of
>           LT -> balanceL (insertNode k x a) y b
>           EQ -> Node2 a (k,x) b
>           GT -> balanceR a y (insertNode k x b))
>   where balanceL (Left a) x b = Node2 a x b
>         balanceL (Right (a,x,b)) y c = Node3 a x b y c
>         balanceR a x (Left b) = Node2 a x b
>         balanceR a x (Right (b,y,c)) = Node3 a x b y c
> insertNode k x (Node3 a y b z c) =
>   case compareKey k y of
>     LT -> balanceL (insertNode k x a) y b z c
>     EQ -> Left (Node3 a (k,x) b z c)
>     GT ->
>       case compareKey k z of
>         LT -> balanceM a y (insertNode k x b) z c
>         EQ -> Left (Node3 a y b (k,x) c)
>         GT -> balanceR a y b z (insertNode k x c)
>   where balanceL (Left a) x b y c = Left (Node3 a x b y c)
>         balanceL (Right (a,x,b)) y c z d = Right (Node2 a x b,y,Node2 c z d)
>         balanceM a x (Left b) y c = Left (Node3 a x b y c)
>         balanceM a x (Right (b,y,c)) z d = Right (Node2 a x b,y,Node2 c z d)
>         balanceR a x b y (Left c) = Left (Node3 a x b y c)
>         balanceR a x b y (Right (c,z,d)) = Right (Node2 a x b,y,Node2 c z d)

> compareKey :: Ord a => a -> (a,b) -> Ordering
> compareKey k1 (k2,_) = compare k1 k2

\end{verbatim}
Deletion also uses an auxiliary function. This function returns the
new node after the element has been deleted together with a boolean
flag that indicates whether the height was decremented.
\begin{verbatim}

> deleteFromFM :: Ord a => a -> FM a b -> FM a b
> deleteFromFM x xys = snd (deleteNode x xys)

> deleteNode :: Ord a => a -> FM a b -> (Bool,FM a b)
> deleteNode _ Empty = (False,Empty)
> deleteNode x (Node2 a y b) =
>   case compareKey x y of
>     LT -> balanceL (deleteNode x a) y b
>     EQ
>       | nullFM a -> (True,b)
>       | otherwise -> balanceR a u (deleteNode (fst u) b)
>       where u = findMin b
>     GT -> balanceR a y (deleteNode x b)
>   where balanceL (False,a) x b = (False,Node2 a x b)
>         balanceL (True,a) x (Node2 b y c) = (True,Node3 a x b y c)
>         balanceL (True,a) x (Node3 b y c z d) =
>           (False,Node2 (Node2 a x b) y (Node2 c z d))
>         balanceR a x (False,b) = (False,Node2 a x b)
>         balanceR (Node2 a x b) y (True,c) = (True,Node3 a x b y c)
>         balanceR (Node3 a x b y c) z (True,d) =
>           (False,Node2 (Node2 a x b) y (Node2 c z d))
> deleteNode x (Node3 a y b z c) =
>   (False,
>    case compareKey x y of
>      LT -> balanceL (deleteNode x a) y b z c
>      EQ
>        | nullFM a -> Node2 b z c
>        | otherwise -> balanceM a u (deleteNode (fst u) b) z c
>        where u = findMin b
>      GT ->
>        case compareKey x z of
>          LT -> balanceM a y (deleteNode x b) z c
>          EQ
>            | nullFM c -> Node2 a y b
>            | otherwise -> balanceR a y b u (deleteNode (fst u) c)
>            where u = findMin c
>          GT -> balanceR a y b z (deleteNode x c))
>   where balanceL (False,a) x b y c = Node3 a x b y c
>         balanceL (True,a) x (Node2 b y c) z d = Node2 (Node3 a x b y c) z d
>         balanceL (True,a) w (Node3 b x c y d) z e =
>           Node3 (Node2 a w b) x (Node2 c y d) z e
>         balanceM a x (False,b) y c = Node3 a x b y c
>         balanceM a x (True,b) y (Node2 c z d) = Node2 a x (Node3 b y c z d)
>         balanceM a w (True,b) x (Node3 c y d z e) =
>           Node3 a w (Node2 b x c) y (Node2 d z e)
>         balanceR a x b y (False,c) = Node3 a x b y c
>         balanceR a x (Node2 b y c) z (True,d) = Node2 a x (Node3 b y c z d)
>         balanceR a w (Node3 b x c y d) z (True,e) =
>           Node3 a w (Node2 b x c) y (Node2 d z e)

> findMin :: Ord a => FM a b -> (a,b)
> findMin (Node2 a x _)
>   | nullFM a = x
>   | otherwise = findMin a
> findMin (Node3 a x _ _ _)
>   | nullFM a = x
>   | otherwise = findMin a

\end{verbatim}
Looking up an element is trivial.
\begin{verbatim}

> lookupFM :: Ord a => a -> FM a b -> Maybe b
> lookupFM _ Empty = Nothing
> lookupFM x (Node2 a y b) =
>   case compareKey x y of
>     LT -> lookupFM x a
>     EQ -> Just (snd y)
>     GT -> lookupFM x b
> lookupFM x (Node3 a y b z c) =
>   case compareKey x y of
>     LT -> lookupFM x a
>     EQ -> Just (snd y)
>     GT -> lookupFM x (Node2 b z c)

\end{verbatim}
The function \texttt{toListFM} returns an association list of all
elements in the map. We use a functional difference list approach
similar to \texttt{show} in order to achieve an efficiency which is
linear in the number of elements in the finite map.
\begin{verbatim}

> toListFM :: Ord a => FM a b -> [(a,b)]
> toListFM = flip elems []
>   where elems Empty xs = xs
>         elems (Node2 a x b) xs = elems a (x : elems b xs)
>         elems (Node3 a x b y c) xs = elems a (x : elems b (y : elems c xs))

\end{verbatim}
Two finite maps are considered equal if they contain the same
elements. Note that the representation trees of the two maps may be
different. Therefore we must use the list of elements in order to
compare the maps.
\begin{verbatim}

> instance (Ord a,Eq b) => Eq (FM a b) where
>   xys1 == xys2 = toListFM xys1 == toListFM xys2

\end{verbatim}
When we display a finite map we will show only its semantic
information not the underlying tree representation.
\begin{verbatim}

> instance (Ord a,Show a,Show b) => Show (FM a b) where
>   showsPrec p xys =
>     showChar '{' . showList (map showAssoc (toListFM xys)) . showChar '}'
>     where showList = flip (foldr ($)) . intersperse (showChar ',')       -- $
>           showAssoc (x,y) = showsPrec 0 x . showString "|->" . showsPrec 0 y

\end{verbatim}
A finite map is a functor with respect to its data argument.
\begin{verbatim}

> instance Ord a => Functor (FM a) where
>   fmap f Empty = Empty
>   fmap f (Node2 a (k,x) b) = Node2 (fmap f a) (k,f x) (fmap f b)
>   fmap f (Node3 a (k,x) b (l,y) c) =
>     Node3 (fmap f a) (k,f x) (fmap f b) (l,f y) (fmap f c)

\end{verbatim}
The function \texttt{checkTree} verifies that a 2-3 tree is actually
balanced. The function returns the height of the tree.
\begin{verbatim}

> checkTree :: Ord a => FM a b -> Int
> checkTree Empty = 0
> checkTree (Node2 a _ b)
>   | h == checkTree b = h + 1
>   | otherwise = error "checkTree: unbalanced 2-3 tree"
>   where h = checkTree a
> checkTree (Node3 a _ b _ c)
>   | h == checkTree b && h == checkTree c = h + 1
>   | otherwise = error "checkTree: unbalanced 2-3 tree"
>   where h = checkTree a

\end{verbatim}
