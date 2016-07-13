-- This is a stripped down example of a possible translation of
-- overloaded numeric literals in a dictionary based implementation of
-- type classes.

-- Note that using this translation in the compiler would be problematic
-- because a non-deterministic choice occurs even when coin is applied to
-- a literal constant, e.g., coin 0.

data Eq a = Eq{ (==), (/=) :: a -> a -> Bool }
data Num a = Num{ inst_Eq_Num :: Eq a, (+), (-), (*) :: a -> a -> a, fromInt :: Int -> a }

inst_Eq_Int = Eq{ (==) = (Prelude.==), (/=) = (Prelude./=) } :: Eq Int
inst_Num_Int = Num{ inst_Eq_Num = inst_Eq_Int, (+) = (Prelude.+), (-) = (Prelude.-), (*) = (Prelude.*), fromInt = id } :: Num Int

inst_Eq_Float = Eq{ (==) = (Prelude.==), (/=) = (Prelude./=) } :: Eq Float
inst_Num_Float = Num{ inst_Eq_Num = inst_Eq_Float, (+) = (Prelude.+), (-) = (Prelude.-), (*) = (Prelude.*), fromInt = Prelude.fromInt } :: Num Float

-- NB A straightforward definition of coin requires non-linear parameters
-- so that fromInt is applied to the dictionary from coin's first argument.
-- The actual implementation below uses an ugly workaround to apply fromInt
-- to that dictionary.
--coin d (fromInt d 0) = True
--coin d (fromInt d 1) = True
coin d n = coin' n
  where coin' (fromInt' 0) = True
  	coin' (fromInt' 1) = True
	fromInt' = fromInt d

main =
   print (findall (\x -> coin inst_Num_Int x)) >>
   print (findall (\x -> coin inst_Num_Float x))
