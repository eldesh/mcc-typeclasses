-- Missing instance caused by incompatible types in different equations
f True x = x == x
f False x | (x::Success) = True
