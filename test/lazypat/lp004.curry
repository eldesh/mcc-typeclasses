-- Here are some examples with lazy patterns and data type contexts.

-- The first example derives from a note in the ghc type checker, which
-- in turn was made public via the Haskell Weekly News. The important
-- point is that the context of the lazy pattern is not used to satisfy
-- the Num a constraint from the body, since the corresponding argument
-- is not evaluated at all. Note that the comment in the ghc sources
-- lacks the asTypeOf application and has no type signature either, which
-- makes the example quite pointless because the types of x and the
-- literal 3 would be completely unrelated.

data C a = Num a => C a

-- f has type Num a => C a -> a
f ~(C x) = 3 `asTypeOf` x

-- g has type Num a => C a -> Maybe a
g ~(C x) = Just (x + x)


-- While right hand side constraints of a data constructor are simply
-- ignored in lazy patterns, left hand constraints must be retained
-- according to the (debatable) Haskell'98 semantics.

data Eq a => T a = T a

-- h has type (Eq a,Num b) => T a -> b
h ~(T _) = 0


-- This function is part of the Haskell Prelude, but may not be
-- defined in the Curry Prelude.
asTypeOf :: a -> a -> a
asTypeOf = const
