-- This is example is supposed to fail with a type signature too
-- general error (Eq a => a vs. inferred type IO ()), not with
-- a missing instance Eq (IO ()) error.
f :: Eq a => a
f = putStr ""
