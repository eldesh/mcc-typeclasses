-- Here is just another tricky example with overloaded numeric literals.
-- The important point here is that the compiler must not naively replace
-- the overloaded numeric literal 0 by a pattern variable z together with
-- with a guard z==0 in the first two alternatives because then the
-- second component of the pair would be evaluated before the first.

f xy =
  case xy of
    (0,False) -> 'a'
    (0,True)  -> 'b'
    (_,_)     -> 'c'

main = print (f (1::Rational,undefined))
