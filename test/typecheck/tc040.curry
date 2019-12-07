-- This example checks that right hand side contexts from a pattern in a
-- do statement or list comprehension qualifier do not shadow any type
-- class constraints introduced earlier in the do expression or list
-- comprehension, which would result in an internal error during the
-- dictionary transformation.

data T a = Eq a => C a

f1 xs = [x | y <- map C xs, C x <- [y], x == x]
f1' xs = [x | C x <- map C xs, x == x]
f1'' cs = [x | C x <- cs, x == x]

f2 x = do { c <- return (C x); C y <- return c; return (y == y); print y }
f2' x = do { C y <- return (C x); return (y == y); print y }
f2'' c = do { C y <- return c; return (y == y); print y }
