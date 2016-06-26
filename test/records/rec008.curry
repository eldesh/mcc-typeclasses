-- Field labels must use consistent types. However, this is checked only
-- after expanding type synonyms.

data T = T1{ name :: [Char] } | T2{ name :: String }
