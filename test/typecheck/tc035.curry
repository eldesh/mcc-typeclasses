-- This is a subtle variant of tc034.curry. The type inferred for the
-- local function g is
--   Eq (_f b) => (a -> b) -> Bool
-- (see tc034.curry for a discussion of that type).
-- for g, where the apparently ambiguous type variable _f is bound in
-- the type environment (namely in the type of f's argument xs) and
-- therefore not reported as ambiguous. In the body of f's definition
-- the type variable _f is then instantiated to the list type constructor
-- due to the null xs application. This means that the context of g's
-- type is now
--   Eq [b] => (a -> b) -> Bool
-- and thus no longer in normal form. Fortunately, the dictionary
-- transformation does not care much about this. The only downside is
-- that compiler will not specialize the (==) application inside g's
-- definition to use the list instance implementation but rather look up
-- the method implementation in the Eq [b] dictionary argument passed
-- to g. (See also tc034.curry and tc036.curry for variants of this
-- example.)

f xs = g (const 'a') && g (const False) && not (null xs)
  where g h = fmap h xs == fmap h xs

main = f [0::Int] =:= True &> f "abc" =:= True
