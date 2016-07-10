-- Detect missing instance from argument expression
-- NB This error manifests itself in the type inferred for (==), which
-- is not general enough (see also ic006.curry for a variant of this
-- example).

data U = U
data T x y = T U y

instance Eq y => Eq (T x y) where
  x == y =
    case x of
      T x1 x2 ->
        case y of
	  T y1 y2 ->
	    x1 == y1 && x2 == y2
