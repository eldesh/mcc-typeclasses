-- This is example 1 from Antoy, Hanus. Programming with Function Patterns.

lengthUpToRepeat (p++[r]++q)
  | nub p == p && elem r p = length p + 1

solve = lengthUpToRepeat . chain

main = print (findfirst (\n -> n =:= solve 123))

chain n = iterate step n
step n = number nsDesc - number nsAsc
  where ns = digits n
        nsAsc = sort (<) ns
	nsDesc = sort (>) ns

-- Auxiliary functions
nub [] = []
nub (x:xs) = x : filter (x /=) (nub xs)

digits n = if n > 0 then digits (n `div` 10) ++ [n `mod` 10] else []
number ns = foldl (\n d -> 10*n + d) 0 ns

sort p xs = foldr insert [] xs
  where insert x [] = [x]
        insert x (y:ys) = if not (p x y) then y : insert x ys else x : y : ys
