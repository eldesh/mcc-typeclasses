-- Check that type synoyms can have higher kinds
-- This one particularly tests the correct handling of (partial)
-- application of the arrow type constructor.

type IntFun = (->) Int
type IntFun' a = IntFun a

data T f a = T (f a)

imap :: (a -> b) -> T IntFun a -> T IntFun b
imap f (T g) = T (f . g)

ifun :: T IntFun a -> Int -> a
ifun (T f) = f

ifun' :: T IntFun a -> IntFun' a
ifun' (T f) = f
