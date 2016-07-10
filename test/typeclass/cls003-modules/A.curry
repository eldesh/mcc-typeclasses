-- NB This module delibarately does not export method z. Obviously,
--    this method must have a default implementation to be useful at
--    all.

module A(Z, zero) where

class (Num a) => Z a where { z :: a; z = 0 }

zero = z
