-- Here is an extremly bizarre example that could lead to a failed
-- assertion in the implementation of (=:<=) when using the purely
-- copying runtime system configuration[*] and the implementation
-- replaces occurrences of duplicate variables by indirection nodes
-- too early.
-- [*] The same error could happen in the standard, trailing
-- configuration, too, if the two continuations returned from the
-- initial try application were continued in the global search space
-- (cf. fpat007.curry).

-- NB The normal forms of pat x y xs are ([],[],True) and (_:_,_:_,False).
--    It is important that x is used (at least) twice before the
--    non-deterministic choice occurs.
pat x y xs = (const const x x y, const x y, null x)

f (pat _ _ _) = True

goal x = f (unknown,unknown,x)

main = print (findall goal)
