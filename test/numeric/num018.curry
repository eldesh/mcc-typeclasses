-- This example demonstrates a rather arcane property of Haskell's
-- pattern matching semantics for (numeric) literals: Alternatives
-- matching different numeric literals are not necessarily mutually
-- exclusive.

instance Num () where
  () + () = ()
  () - () = ()
  () * () = ()
  negate () = ()
  abs () = ()
  signum () = ()
  fromInteger _ = ()

test1 u b =
  case (u,b) of
    (0,False) -> 'a'
    (1,True) -> 'b'
test2 u b =
  case u of
    0 | b == False -> 'c'
    1 | b == True -> 'd'

main = putStrLn [test1 () True,test2 () True]
