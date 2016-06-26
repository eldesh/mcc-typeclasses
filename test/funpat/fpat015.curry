-- This file contains a few examples where the old implementation of
-- (=:<=) had troubles noticing that a variable was bound more than
-- once.

dup x = (x,x)

goal1 x = dup x =:<= (unknown, failed)
goal2 x = dup (id x) =:<= (unknown, failed)
goal3 = dup unknown =:<= (unknown, failed)
