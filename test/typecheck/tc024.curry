-- Missing instance caused by incompatible types in different
-- functions of the same binding group
f x = g x
  where g y | y == y = h x
        h z = putStr "" >> z >> g x
