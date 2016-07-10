-- Expression type signature is more general than the inferred type
f _ = (success :: Eq a => a)
