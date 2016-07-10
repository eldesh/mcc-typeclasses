-- This test checks the correct assignment of precedences within the body
-- of an instance declaration. In order for the op instance method
-- definition to be valid, the compiler must use the local precedence of
-- op (which is lower than that of (:)) and not the one of the class
-- imported from module A (see also cls014.curry and cls015.curry for
-- variants of this test).

module cls016 where
import A

class D a where
  infix 4 `op`
  op :: a -> a -> a

instance D [a] where
  []   `op` ys = ys
  x:xs `op` ys = x : (xs `cls016.op` ys)
