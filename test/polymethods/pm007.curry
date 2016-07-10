-- Basic test for polymorphic methods, a simple polymorphic function,
-- a (monomorphic) instance of the class, plus a function that uses it
-- (at two different types).

class C a where
  -- NB type class variable does not appear first in the method's type
  f :: b -> a

instance C Integer where
  f _ = 0

-- NB When complying strictly to the Haskell report, the list requires
--    a type signature because the type of main is (Num a, C a) => IO a
--    and numeric default resolution does not apply because the constraint
--    involves the non-standard class C. MCC is more forgiving here at
--    present.
main = print ([0,f False,f 'a'])

