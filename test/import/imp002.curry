-- NB ``import M as Prelude'' does not qualify as an import of the
--    Prelude. Thus all Prelude entities are in scope below and
--    therefore all operators are ambiguous.
import A as Prelude

f (x,y,z,t) = x*x Prelude.+ y*y Prelude.+ z*z Prelude.- t*t
