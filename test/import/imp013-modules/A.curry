module A(f,g) where

data T = T
class C a
instance C T

f :: C a => a -> Bool
f _ = True

g = T
