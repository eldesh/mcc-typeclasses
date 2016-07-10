module A where
class C a where f :: Integer -> a
class C a => D a where g :: a -> Integer
