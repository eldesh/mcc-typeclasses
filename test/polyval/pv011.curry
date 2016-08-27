-- An example that checks that record constructions for non-constant
-- constructors are non-expansive expressions if all field labels are
-- given and hence their types can be generalized.

data List a = Nil | Cons{ hd::a, tl::List a }

main = (Cons [False] l0,Cons "a" l0)
  where l0 = Cons{ hd=[], tl=Nil }

