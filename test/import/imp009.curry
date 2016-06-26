-- This test checks that the unit, list, and tuple types are exported
-- from the Prelude if the Prelude has and explicit export list (see
-- also imp007.curry and imp008.curry for variants of this test)
main = doSolve (linear (concatMap swap [(False,True),(True,False)]) =:=
                [True,False,False,True])
  where swap (x,y) = [(y,x)]
        linear [] = []
        linear ((x,y) : xys) = x : y : linear xys
