-- This is a more elaborate variant of der002.curry, which shows why only
-- assertions of the form C u are allowed in instance contexts, where u
-- is a type variable. In the code below, the compiler would infer the
-- context
--   (Eq a, Eq (f (T f a)))
-- for T's derived Eq instance. Obviously, this context could lead to
-- non-termination of context reduction if the compiler were ever going
-- to reduce an Eq (T f a) assertion. Hbc, which allows general
-- assertions in instance contexts, crashes with a stack overflow when
-- checking the definition of function f. Hugs reaches the cutoff limit
-- while checking the definition of function g. Only ghc is able to
-- compile both definitions.
-- See also ../typeclass/cls009.curry, which checks that an explicit Eq
-- instance cannot be declared for T (rather its simpler variant from
-- der002.curry) cannot be declared either.

data T f a = U a | T (f (T f a)) deriving (Eq)

f x y = U x == y || T [] == y
g y = f () y

