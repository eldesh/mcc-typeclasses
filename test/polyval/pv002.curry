-- This example of a polymorphic variable binding is really a function
-- binding in disguise
main = (list 1, list 'a')
  where list = \x -> [x]
