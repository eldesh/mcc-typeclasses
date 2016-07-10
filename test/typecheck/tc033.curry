-- The example below is quite tricky because the type of the local
-- function g is (Eq (m _a),Monad m) => b -> T m _a where _a is the
-- (non-generalizable) type variable representing the type of the
-- argument x. Therefore, we can use g at two different monad's in f's
-- body.
-- NB This example is accepted by both Hugs and ghc, whereas nhc98 and
--    hbc complain about the Eq (m _a) context.

data T f a = T (f a)

f x = (let T (Just y) = g () in y, let T [z] = g () in z)
  where g u | v == return x = T v where v = return x

main = print (f 'a')
