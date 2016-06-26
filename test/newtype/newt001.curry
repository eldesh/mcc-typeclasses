-- Newtype constructors are transparent with respect to the operational
-- semantics. The compiler therefore replaces saturated newtype
-- constructor applications in patterns and expressions by their
-- argument. This does not work for partial applications of newtype
-- constructors and this test checks that they are handled correctly by
-- the compiler, too.
module newt001 where
import A
newtype Pair a b = Pair (a,b) deriving Show

main = print (map A.Pair [(1,2)]) >> print (map newt001.Pair [(1,2)])
