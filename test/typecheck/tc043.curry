-- This example checks that the left hand and right hand side contexts in
-- a data type declaration are managed properly by the compiler even in
-- cases where the type constraints overlap.

import A

incr (C1 x) = C1 (x + 1)
tautology (C2 x) = x == x
