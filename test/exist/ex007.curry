-- Skolem type escapes its scope (only) through the context

data Key a = forall b . Key b (b -> a)

bad (Key x f) xs = fmap (const x) xs == fmap (const x) xs

