-- This example checks that pattern variables are evaluated properly
-- after they are bound to an unevaluated term. At one point during
-- development, one of the two constraints below (the second) failed
-- because the lazy application unknown was not evaluated.

main =
  do
    doSolve ((x,x) =:<= (take 10 (repeat 'a'),unknown)) >> putStrLn x
    doSolve ((y,y) =:<= (unknown,take 10 (repeat 'b'))) >> putStrLn y
  where x,y free
