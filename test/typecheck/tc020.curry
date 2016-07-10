-- Context handling with non-local variables in explicitly type
-- variable. The inferred type for f should be
-- f :: (Eq a,Show b) => a -> b
f x = (true (x==x) &> undefined) :: Show a => a
  where true True = success
