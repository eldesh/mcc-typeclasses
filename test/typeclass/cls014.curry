-- This test checks the correct assignment of precedences within the body
-- of an instance declaration. In order for the op instance method
-- definition to be valid, the compiler must use the precedence of A.op
-- (which is lower than that of (:)) and not the default precedence of
-- the local op operator (see also cls015.curry and cls016.curry for
-- variants of this test).

import A
infixl 7 `op`

op :: Int -> Int -> Int
op = (+)

instance C [a] where
  []   `op` ys = ys
  x:xs `op` ys = x : (xs `A.op` ys)
