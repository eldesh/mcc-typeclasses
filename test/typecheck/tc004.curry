-- This example is due to Mark Jones' Typing Haskell in Haskell paper
-- The compiler infers type Bool -> Bool for both f and g.
f x = (x==x) || g True
g y = (y<=y) || f True
