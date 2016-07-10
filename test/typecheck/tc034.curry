-- Another tricky example. The type and context inferred for the local
-- function g are
--   (Functor _f, Eq (_f b)) => (_a -> b) -> Bool
-- where the type of f's argument xs is _f _a. The Functor _f constraint
-- is clearly lifted into f's body since the type variable _f is bound
-- in the environment. However, the Eq (_f b) constraint presents a
-- problem. If the constraint were lifted, the type variable b could not
-- be generalized (otherwise, it would be ambiguous in f's body). On
-- the other hand, if the constraint is not lifted, g's type is
-- ambiguous because the type variable _f does not appear in the plain
-- type.
-- Nevertheless, the code below is perfectly reasonable (and accepted
-- by Hugs and ghc). In order to accept this definition, the compiler
-- keeps constraints for type variables which are bound in the initial
-- type environment and does not report those type variables as ambiguous
-- even if they do not appear in the plain type. Thus, the compiler infers
-- type
--   Eq (_f b) => (a -> b) -> Bool
-- for g.
-- NB This example (after using booleans instead of constraints in the
--    main function) is accepted by both Hugs and ghc, whereas nhc98 and
--    hbc complain about the Eq (_f b) context.
-- (See also tc035.curry and tc036.curry for variants of this example.)

f xs = g (const 'a') && g (const False)
  where g h = fmap h xs == fmap h xs

main = f (Just (0::Int)) =:= True &> f "abc" =:= True
