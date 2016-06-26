-- Make sure that the unit, list, and tuple types are available even
-- when the Prelude's entities are imported with qualified names only
-- (see also imp005.curry for a variant of this test).
import qualified Prelude

unit () = ()
swap (x,y) = (y,x)
rotL3 (x,y,z) = (y,z,x)
rotL3 (x,y,z) = (z,x,y)

rev [] = []; rev (x:xs) = app (rev xs) [x]
app [] ys = ys; app (x:xs) ys = x : app xs ys

-- Note: swapInit will not compile if the precedence of the (:) constructor
--       is not available
swapInit (x1:x2:xs) = x2:x1:xs; swapInit :: [a] -> [a]
