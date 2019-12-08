-- Since function patterns effectively get transformed into additional
-- guard expressions in the scope of the function pattern, nested
-- patterns within the arguments of a function pattern cannot be used to
-- dynamically introduce type class instances for their own
-- arguments. Instead, those instances must be provided by the context.

data T a = Eq a => C a
f (C c) = c
g (f (C c)) | c == c = c
g' fp = case fp of f (C c) | c == c -> c
