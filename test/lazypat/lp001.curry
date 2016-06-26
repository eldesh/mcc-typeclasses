-- Lazy patterns are convenient syntactic sugar for matching components
-- of data terms without actually evaluating the argument before one of
-- the components is used. Note that there is a subtle issue when mixing
-- as-patterns with lazy patterns: Consider ~(x@t) vs. x@(~t). When x is
-- evaluated for the former, the pattern t is matched with the
-- corresponding argument expression. On the other hand, when x is
-- evaluated for the latter the pattern t is not matched with the
-- argument expression.

f ~x@(Just _) = [x::Maybe Int]
g x@ ~(Just _) = [x::Maybe Int]

main = mapIO (print . findall) [\x -> x =:= f Nothing,\x -> x =:= g Nothing]
