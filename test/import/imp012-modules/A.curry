-- NB deliberatly do not export K
module A(run,return,(>>=)) where
import qualified Prelude
infixl 0 >>=

newtype K r a = K ((a -> r) -> r)

run :: K a a -> a
run (K k) = k Prelude.id

return :: a -> K r a
return x = K (\f -> f x)

(>>=) :: K r a -> (a -> K r b) -> K r b
K k >>= f = K (\g -> k (\x -> let K k' = f x in k' g))
