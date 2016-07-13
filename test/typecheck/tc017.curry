-- Expression type signature is more general than the inferred type
f _ = (putStr "" :: Eq a => a)
