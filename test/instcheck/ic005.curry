-- Detect missing instance from argument expression

data U z = U
data T x y = T x (U y) deriving Eq
