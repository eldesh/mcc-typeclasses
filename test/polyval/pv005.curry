-- This example shows that non-expansive expressions may involve local
-- let declarations (provided that their bindings are non-expansive
-- themselves).
main = (list False, list 'a')
  where list = \x -> [(n,x)] where n = 1
