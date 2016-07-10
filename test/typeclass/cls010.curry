-- Only constraints of the form C u are allowed in class declaration contexts

class (Eq (f Int)) => C f where
  f :: Int -> f Int -> Bool
