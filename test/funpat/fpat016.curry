-- Here is a contrived example that suspends if equality constraints
-- between the values bound to a single variable are evaluated strictly
-- from left to right.

infixr 0 &&>
True &&> x = x

dup x  = (x,x)
triple x = (x,x,x)

f (dup x) = x
g (triple x) = x

goal1 = f (x == 1 &&> x, x =:= 1 &> x) where x free
goal2 = g (unknown, x == 1 &&> x, x =:= 1 &> x) where x free
