-- The "standard" example for existential types

data Key a = forall b . Key b (b -> a)

key (Key x f) = f x

main = print (map key [Key "abc" length, Key 17 (+ 25), Key '\096' ord])
