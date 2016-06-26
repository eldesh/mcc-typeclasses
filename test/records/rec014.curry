-- This example checks that the import path is not relevant with respect
-- to whether a field label can be used with a particular record pattern
-- or expression. It does not even matter if the field labels are
-- exported individually and without their type. Note that the import
-- specifications match the export specifications of the corresponding
-- modules exactly. (See also rec013.curry for a variant of this
-- example.)

module rec014 where
import qualified B(T(T))
import qualified C(left)
import qualified D(right)

swapT B.T{ C.left=x, D.right=y } = B.T{ C.left=y, D.right=x }
swap2T t = t{ C.left = D.right t, D.right = C.left t }
