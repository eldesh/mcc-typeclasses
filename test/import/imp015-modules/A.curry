module A where
data (Bounded a, Ord b) => T a b = B a | O b | BO a b
