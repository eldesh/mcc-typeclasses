-- Very contrived example with multiple occurrences of the same field
-- label in the definition of a data constructor.

data T = L{ key::Int, key::Int, key::Int }
       | R{ key::Int, key::Int }
