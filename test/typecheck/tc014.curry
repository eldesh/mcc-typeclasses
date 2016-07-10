-- This is example is supposed to fail with a type signature too
-- general error (Eq a => a vs. inferred type Success), not with
-- a missing instance Eq Success error.
f :: Eq a => a
f = success
