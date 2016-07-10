-- This is minor variant of kc001.curry, which shows that the compiler
-- must take default class method implementations into account when
-- computing minimal declaration groups for kind inference.
-- Note that the compiler reports an error when asTypeOf is defined as
-- asTypeOf = const because all local variables must have monomorphic
-- types.

data C a => D a = Foo (S a)
type S a = [D a]
class C a where
  bar :: a -> Bool
  bar x = case Foo [] `asTypeOf` x of Foo xs -> null xs
    where asTypeOf :: D a -> a -> D a
          asTypeOf x y = x
