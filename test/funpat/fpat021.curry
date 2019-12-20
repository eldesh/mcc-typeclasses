-- Since function patterns are effectively transformed into constraint
-- guards, their arguments cannot introduce any dynamic instances, which
-- is similar to lazy patterns. However, in contrast to lazy patterns,
-- the corresponding instances must be present in the environment so that
-- the program can construct the constraint expression at runtime. (See
-- also fpat019.curry and fpat020.curry for variants of this example.)

data Numeric a = Num a => Numeric a

f (id (Numeric x)) = True
g (Numeric x `const` _) = True
