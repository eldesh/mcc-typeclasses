module B where
import Prelude()
import A as Prelude

f (x,y,z,t) = x*x Prelude.+ y*y Prelude.+ z*z Prelude.- t*t
