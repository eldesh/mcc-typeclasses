module A(List(hd,tl), nil,cons,len, Identity(unId),mkId) where

infixr 5 `cons`

data List a = Nil
     	    | Cons{ length::Int, hd::a, tl::List a }

nil = Nil
cons x xs = Cons{ A.length = 1 + len xs, hd = x, tl = xs }
len Nil = 0
len Cons{ A.length = n } = n

newtype Identity a = I{ unId::a }
mkId x = I x
