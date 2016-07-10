-- Test that conflicting instance declarations for the primitive types
-- are detected
import A                          -- imports Functor ((->) a) instance

instance Show () where show () = "()"
instance Show [a] where
  showsPrec _ [] = showString "[]"
  showsPrec _ (_:_) = showString "[...]"
instance Eq x => Eq ([] x) where
  []     == []     = True
  (_:_)  == []     = False
  []     == (_:_)  = False
  (x:xs) == (y:ys) = x==y && xs==ys
instance Eq ((->) a b) where _ == _ = False; _ /= _ = False
instance Eq (a -> b) where _ == _ = False; _ /= _ = False
instance Functor ((->) a) where fmap = (.)
