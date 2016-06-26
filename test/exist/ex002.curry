-- Skolem type escaping its scope

data Key a = forall b . Key b (b -> a)

val (Key x _) = x
