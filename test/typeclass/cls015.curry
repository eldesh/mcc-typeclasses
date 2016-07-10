-- This test checks the correct assignment of precedences within the body
-- of an instance declaration. In order for the op instance method
-- definition to be valid, the compiler must use the precedence of A.op
-- (which is lower than that of (:)) and not the default precedence of
-- the local op operator. As a minor complication we use a qualified type
-- class name and a local alias in the instance declaration (see also
-- cls014.curry and cls016.curry for a variants of this test).

import qualified A as B
infixl 7 `op`

op :: Int -> Int -> Int
op = (+)

instance B.C [a] where
  []   `op` ys = ys
  x:xs `op` ys = x : (xs `B.op` ys)
