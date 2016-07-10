-- This example tests a borderline case of polymorphic recursion. One
-- would expect that this program fails if the type signature for g is
-- omitted because f and g are mutually recursive and therefore g can
-- be used only monomorphically in f without a type signature.
-- However, if the type checker applies type generalization only to
-- those declarations inside a group of mutually recursive
-- declarations that do not have an explicit type signature and checks
-- declarations with explicit type signatures *after* generalization,
-- the declaration below succeeds. This is in fact how the type
-- checker in Mark Jones's Typing Haskell in Haskell paper is
-- implemented and matches the static semantics for function and
-- pattern bindings in the Haskell 2010 report (but not the revised
-- Haskell 98 report). MCC follows the Haskell 2010 report here.

main = print (f [1..3])
  where f :: [a] -> [a]
        f xs = g True xs ++ g 'a' xs
        --g :: a -> [b] -> [b]
        g _ [] = []
        g _ (x:xs) = x : f xs
