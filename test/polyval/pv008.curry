-- An example that checks that record constructions for constant
-- constructors are non-expansive and their types can be generalized.

data List a = Nil | Cons{ hd::a, tl::List a }

main = (Cons False l0,Cons "a" l0)
  where l0 = Nil{}

