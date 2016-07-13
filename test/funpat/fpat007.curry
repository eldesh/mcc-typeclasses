-- Here is an extremly bizarre example that could lead to a failed
-- assertion in the implementation of (=:<=) when the implementation
-- replaces occurrences of duplicate variables by indirection nodes
-- too early. (See fpat006.curry for a variant of this test that does
-- not break encapsulation).

-- NB The normal forms of pat x y xs are ([],[],True) and (_:_,_:_,False).
--    It is important that x is used (at least) twice before the
--    non-deterministic choice occurs.
pat x y xs = (const const x x y, const x y, null x)

f (pat _ _ _) = True

goal x = f (unknown,unknown,x)

main = print (map unpack (try goal))
