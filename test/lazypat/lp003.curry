-- Lazy patterns in rigid case expressions should be match rigidly as
-- well.

goal = case (0:_) of x : ~(y : ys) -> x ? y
