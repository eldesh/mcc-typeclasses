-- Make sure that the unit, list, and tuple types are available even
-- if the Prelude's entities are hidden (see also imp006.curry for a
-- variant of this test).
import Prelude(Success)

unit () = ()
swap (x,y) = (y,x)
rotL3 (x,y,z) = (y,z,x)
rotR3 (x,y,z) = (z,x,y)

rev [] = []; rev (x:xs) = app (rev xs) [x]
app [] ys = ys; app (x:xs) ys = x : app xs ys

-- Note: swapInit will not compile if the precedence of the (:) constructor
--       is not available
swapInit (x1:x2:xs) = x2:x1:xs; swapInit :: [a] -> [a]
