-- Some examples around equality of partial applications.

-- This example is due to Sebastian Fischer (see his post 'Re: equality
-- of partial applications' from 20. June 2012 19:01 GMT on the Curry
-- mailing list), as an example for an invalid eta-expansion that used to
-- be performed by MCC.
goal1 = let mkId _ = id in mkId () =:= id

-- Here is a variant using a top-level definition
myId _ = id
goal2 = myId () =:= id

-- The following example uses a definition whose expression is a lambda
-- abstraction. The compiler may still convert these into binary
-- functions.
f1 xs = \z -> foldr (*) z xs :: Int
goal3 = f1 [0..3] =:= f1 [0..3]

-- Obviously, we cannot eta-expand definitions when pattern matching
-- is involved. Otherwise, we'd incorrectly succeed on the second goal.
f2 xs@(_:_) = \z -> foldr (*) z xs :: Int
goal4 = f2 [0..3] =:= f2 [0..3]
goal5 = f2 [] =:= f2 []

