-- Missing instance for an existentially quantified variable

data Key a = forall b . Key b (b -> a)

eqKey (Key x f) | x == x = f x
