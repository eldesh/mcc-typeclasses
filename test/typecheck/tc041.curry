-- This example checks that the compiler restricts the type constraints
-- from the left hand side context of a data type declaration to the free
-- variables of each data constructor's argument types, but keeps all
-- type constraints from a right hand side context.

data Enum a => EnumSet a
  = Ord a => Empty
  | Ord a => Elem (EnumSet a) a (EnumSet a)

-- zero :: Ord a => EnumSet a
zero = Empty

-- NB It is necessary to use an as-pattern in the first equation to tell
-- the compiler that the Empty tree on the left hand side of the equation
-- and the singleton tree on its right hand side belong to the same type
-- and hence the Ord instance from the Empty constructor can be used for
-- the Elem expression in the body of the equation.

-- add :: Enum a => a -> EnumSet a -> EnumSet a
add x t@Empty = Elem t x t
add x (Elem l y r) =
  case compare x y of
    LT -> Elem (add x l) y r
    EQ -> Elem l y r
    GT -> Elem l y (add x r)
