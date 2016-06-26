-- This example checks that the import path is not relevant with respect
-- to whether a field label can be used with a particular record pattern
-- or expression. Note that the import specifications match the export
-- specifications of the corresponding modules exactly. (See also
-- rec014.curry for a variant of this example.)

module rec013 where
import qualified B(T(T))
import qualified C(T(left))
import qualified D(T(right))

swapT B.T{ C.left=x, D.right=y } = B.T{ C.left=y, D.right=x }
swap2T t = t{ C.left = D.right t, D.right = C.left t }
