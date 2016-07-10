-- Missing instance caused by incompatible types in different
-- functions of a nested binding group
f x = g undefined
  where g y | y == y = h y
        h z = z &> x
