module A where

data Eq a => T1 a = Num a => C1 a
data Num a => T2 a = Eq a => C2 a
