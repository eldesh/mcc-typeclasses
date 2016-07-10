-- Expression type signature that (correctly) restricts the type of
-- an expression.
f x y | (x::Int) == y = success
