-- Ambiguous type caused by explicitly typed expression
f = const 'a' (undefined :: Eq a => a)
