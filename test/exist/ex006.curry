-- A contrived example which shows that existential types can appear in
-- the result of an expression as long as they are defined in an
-- enclosing scope.

data Key a = forall b. Key b (b -> a)
key (Key x f) = f x

data KeyList = KNil | forall a. KCons (Key a) KeyList

tricky KNil = success
tricky (KCons k ks) | (let Key x f = k in f x) =:= key k = tricky ks
