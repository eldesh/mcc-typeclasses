-- This example checks that function patterns can be mixed with boolean
-- guards

f (_ ++ [x,y,z]) n
  | n == 0 = x
  | n == 1 = y
  | n == 2 = z

main = mapIO (print . \n -> findall (\x -> x =:= f "abc" n)) [0..3]
