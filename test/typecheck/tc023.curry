-- Missing instance caused by incompatible types in different equations
f True x = return (x == x)
f False x = putStr "" >> x
