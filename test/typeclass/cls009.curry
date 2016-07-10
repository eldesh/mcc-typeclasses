-- This example fails because (derived) instance contexts are
-- restricted to assertions of the form C u, where u is a type
-- variable. Note that it is neither possible to derive the Eq
-- T instance (see ../deriving/der002.curry and also
-- ../deriving/der003.curry which gives a rationale for this
-- restriction).

data T f a = T (f a)
instance Eq (f a) => Eq (T f a) where
  T x == T y = x == y

