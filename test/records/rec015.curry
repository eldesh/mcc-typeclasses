-- This example tests that the syntax T{} works correctly for all
-- constructors in patterns and expressions, regardless of whether the
-- constructor was declared using record syntax or not (cf. Sects. 3.15.2
-- and 3.17.2 of the revised Hakell'98 report).

notNull []    = False                     -- NB []{} is not a legal expression!
notNull (:){} = True

consP (:){} = success

main | notNull (:){} && (consP xs &> True) = doSolve (xs =:= "Abc") >> print xs
  where xs free
