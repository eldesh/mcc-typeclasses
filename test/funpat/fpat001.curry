-- The translation of function patterns internally uses the constraint
-- (=:<=), which is problematic because it may bind a free variable to an
-- unevaluated expression. This example checks that such variables are
-- nevertheless evaluated and should display the number 4 as result of
-- the goal and not the unevaluated expression 2+2.

last (_ ++ [x]) = x
goal = last (replicate 5 undefined ++ [2+2])
