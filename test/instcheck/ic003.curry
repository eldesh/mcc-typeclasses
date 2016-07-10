-- Detect missing super class instance in explicit instance declaration

data T x y = T x y
instance (Ord x, Ord y) => Ord (T x y) where
  x `compare` y =
    case x of
      T x1 x2 ->
        case y of
	  T y1 y2 ->
	    case compare x1 y1 of
	      LT -> LT
	      EQ -> compare x2 y2
	      GT -> GT
