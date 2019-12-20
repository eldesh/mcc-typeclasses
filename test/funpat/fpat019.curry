-- Since function patterns are effectively transformed into constraint
-- guards, their arguments cannot introduce any dynamic instances, which
-- is similar to lazy patterns. However, in contrast to lazy patterns,
-- the corresponding instances must be present in the environment so that
-- the program can construct the constraint expression at runtime. In
-- particular, this means that it is impossible to use data constructors
-- with constrained existentially quantified variables in an argument of
-- a function pattern. (See also fpat020.curry and fpat021.curry for
-- variants of this example.)

data Showable = forall a. Show a => Showable a

f (id (Showable x)) = showsPrec 0 x
