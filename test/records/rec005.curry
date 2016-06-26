-- Field labels share a name space with constructors and top-level
-- functions.

data T1 a = T1{ key :: Int, val :: a }
data T2 a = T2{ T1 :: a }
data T3 a = T3{ f :: a }
newtype N a = N{ val :: a }

f x y = (x,y)

