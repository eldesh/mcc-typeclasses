-- When updating pattern bindings, one has to be careful about the
-- interaction with update frames. For instance, when ys is evaluated in
-- the body of f, its node is overwritten with an indirection pointing to
-- the queue-me node of f's own application.

f xys = let (xs,ys) = unzip xys in const ys xs
main = print (length (f [(1,2)]))
