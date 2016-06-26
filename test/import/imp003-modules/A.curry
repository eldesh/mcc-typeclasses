module A(module A,module Prelude) where
import Prelude hiding((+),(-),(*),div,mod)
import qualified Prelude

infixl 7 *, /
infixl 6 +, -

(+) = (Prelude.+) :: Float -> Float -> Float
(-) = (Prelude.-) :: Float -> Float -> Float
(*) = (Prelude.*) :: Float -> Float -> Float
(/) = (Prelude./) :: Float -> Float -> Float
