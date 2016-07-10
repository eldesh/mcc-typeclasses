-- This example is due to Mark Jones' Typing Haskell in Haskell paper
-- The compiler infers type Bool -> Bool for g.
f :: Eq a => a -> Bool
f x = (x==x) || g True
g y = (y<=y) || f True
