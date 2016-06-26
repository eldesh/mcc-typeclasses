module A(nil, cons, isNil, hd, tl) where

infixr 5 `cons`

nil = Nil
cons = Cons

data List a = Nil | Cons { hd::a, tl :: List a }

isNil Nil = True
isNil Cons{} = True
