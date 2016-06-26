-- Type inference uses fresh skolem types for each occurrence of a data
-- constructor with existentially quantified argument types. During case
-- flattening, such occurrences might get merged into a single case
-- alternative and the compiler must handle this correctly. (See also
-- ex003.curry and ex005.curry for variants of this example.)

data Ex a = forall b . Ex Bool (a -> b) b (b -> a)

f (Ex True f x g) z = (Ex True f (f z) g,g x)
f ex@(Ex False _ _ _) z = (ex,z)

main =
  snd (f (Ex True (flip replicate ' ') "abc" length) 1) =:=
  snd (f (Ex False undefined undefined undefined) 3)
