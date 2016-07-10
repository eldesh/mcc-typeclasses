-- NB local type signature is necessary; otherwise the application f "Hello"
--    is rejected because f's inferred type would be [Int] -> [Int].
main = x =:= (1::Int) &> f "Hello"
  where (x:xs) = f (repeat unknown)
        f (y:ys) = y : if x<=x then [] else f ys
