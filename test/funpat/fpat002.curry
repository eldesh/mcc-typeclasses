-- This example tests that variables which occur more than once in the
-- final pattern are evaluated to normal form

dup x = (x,x)
f (dup _) = success
goal1 _ = f (unknown,failed)
goal2 _ = f (failed,unknown)
