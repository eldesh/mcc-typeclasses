-- Here are a few examples with pattern declarations that the compiler
-- can simplify at compile time.

-- The patterns in the equations of f1, f2, and f3 can be matched completely
-- at compile time. Moreover, the pattern variables in f1 can be subject to
-- alias substitution.
f1 = let us free; (xs,ys) = (us,us) in Just (xs ++ ys)
f2 = let (xs,ys) = (unknown++[],unknown++[]) in Just (xs ++ ys)
f3 = let (c:cs) = "abc" in Just (cs ++ [c])

-- The patterns in the equations of g1 and g2 fail, i.e., all pattern
-- variables can be bound to Prelude.failed.
g1 = let (x:xs) = [] in Just (xs ++ [x])
g2 = let (x:xs,ys) = ([],[]) in Just (xs ++ x : ys)

-- The patterns in the equations of h1 and h2 can be matched partially
-- at compile time. The pattern variable ys in u1 can be subject to
-- alias substitution.
h1 = let us free; (x:xs,ys) = (unknown,us) in Just (xs ++ x : ys)
h2 = let (x:xs,ys) = (unknown++[],unknown++[]) in Just (xs ++ x : ys)

-- This last test demonstrates that the compiler must be careful when
-- simplifying partial matches of pattern bindings. Even though the value
-- bound to ys is known and x is not used in the body of h, the
-- evaluation of the goal h [] must fail.
main = print (findall (\z -> z =:= h []))
  where h xs = Just ys where (x:_,ys) = (xs,[]::[Int])
