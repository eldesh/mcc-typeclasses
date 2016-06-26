-- This example shows that function patterns can be used in pattern
-- declarations (and thus can be matched lazily). Note that the
-- parentheses around the pattern are necessary (and sufficient) to
-- prevent interpretation as a local function declaration. Alternatively,
-- we could use a qualified operator and then omit the parentheses, i.e.,
-- where ys Prelude.++ zs = xs.

f xs = (ys,zs) where (ys ++ zs) = xs
g (x : ~(xs ++ ys)) = [[x],xs,ys]

main =
  do
    mapIO print (findall (\xs -> xs =:= f [1..3]))
    print (head (g ('a' : repeat undefined)))
