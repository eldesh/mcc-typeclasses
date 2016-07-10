-- Only constraints of the form C u are allowed instance declaration contexts

data T f = T (f Int)
instance Eq (f Int) => Eq (T f) where
  T xs == T ys = xs == ys
