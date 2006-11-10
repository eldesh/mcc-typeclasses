-- $Id: Numeric.curry 1997 2006-11-10 20:45:06Z wlux $
--
-- Copyright (c) 2003-2006, Wolfgang Lux
-- See ../LICENSE for the full license.

module Numeric(showSigned, showIntAtBase, showInt, showOct, showHex,
               readSigned, readInt, readDec, readOct, readHex,
	       showEFloat, showFFloat, showGFloat, showFloat, 
               readFloat, lexDigits) where
import Char

{- Missing Haskell Prelude definitions -}
type ReadS a = String -> [(a,String)]
{- end of Haskell Prelude definitions -}

showSigned :: (Int -> ShowS) -> Int -> Int -> ShowS
showSigned showPos p x
  | x < 0     = showParen (p > 6) (showChar '-' . showPos (-x))
  | otherwise = showPos x

showIntAtBase :: Int -> (Int -> Char) -> Int -> ShowS
showIntAtBase base intToDig n rest
  | n < 0 = error "Numeric.showIntAtBase: can't show negative numbers"
  | n' == 0 = rest'
  | otherwise = showIntAtBase base intToDig n' rest'
  where n' = n `quot` base
        d  = n `rem` base
	rest' = intToDig d : rest

showInt :: Int -> ShowS
showInt = showIntAtBase 10 intToDigit

showOct :: Int -> ShowS
showOct = showIntAtBase 8 intToDigit

showHex :: Int -> ShowS
showHex = showIntAtBase 16 intToDigit


readSigned :: Num a => ReadS a -> ReadS a
readSigned r cs =
  case dropSpace cs of
    [] -> []
    (c:cs')
      | c == '(' -> [(n,cs''') | (n,cs'') <- readSigned r cs',
                                 cs''' <- case dropSpace cs'' of
			                    (')':cs) -> [cs]
					    _ -> []]
      | c == '-' -> [(negate n,cs'') | (n,cs'') <- r (dropSpace cs')]
      | otherwise -> r (c:cs')
  where dropSpace = dropWhile isSpace

readInt :: Int -> (Char -> Bool) -> (Char -> Int) -> ReadS Int
readInt base isDig digToInt cs =
  case span isDig cs of
    (d:ds,cs') -> [(foldl (\n d -> n * base + digToInt d) (digToInt d) ds,cs')]
    ([],_) -> []

readDec :: ReadS Int
readDec = readInt 10 isDigit digitToInt

readOct :: ReadS Int
readOct = readInt 8 isOctDigit digitToInt

readHex :: ReadS Int
readHex = readInt 16 isHexDigit digitToInt


showEFloat :: Maybe Int -> Float -> ShowS
showEFloat d f = showEFloat (maybe (-1) (max 0) d) f
  where foreign import primitive showEFloat :: Int -> Float -> ShowS

showFFloat :: Maybe Int -> Float -> ShowS
showFFloat d f = showFFloat (maybe (-1) (max 0) d) f
  where foreign import primitive showFFloat :: Int -> Float -> ShowS

showGFloat :: Maybe Int -> Float -> ShowS
showGFloat d f
  | f' >= 0.1 && f' < 1.0e7 = showFFloat d f
  | otherwise = showEFloat d f
  where f' = if f < 0.0 then -. f else f
        
showFloat :: Float -> ShowS
showFloat = showGFloat Nothing


readFloat :: ReadS Float
readFloat r = [(convert ds (k - d),t) | (ds,d,s) <- lexFix r,
                                        (k,t) <- readExp s] ++
              [(0.0/0.0,t) | t <- match "NaN" r] ++
              [(1.0/0.0,t) | t <- match "Infinity" r]
  where lexFix r = [(ds ++ ds',length ds',t) | (ds,s) <- lexDigits r,
                                               (ds',t) <- lexFrac s]
        lexFrac "" = [("","")]
        lexFrac (c:ds)
          | c == '.' && not (null frac) = frac
          | otherwise = [("",c:ds)]
          where frac = lexDigits ds
        readExp "" = [(0,"")]
        readExp (e:s)
          | e `elem` "eE" && not (null exp)  = exp
          | otherwise = [(0,e:s)]
          where exp = readExp' s
        readExp' "" = []
        readExp' (c:s)
          | c == '-' = [(-k,t) | (k,t) <- readDec s]
          | c == '+' = readDec s
          | otherwise = readDec (c:s)
        match prefix s =
          case splitAt (length prefix) s of
            (cs,cs') ->
              [cs' | cs == prefix && (null cs' || not (isAlphaNum (head cs')))]
	convert ds e = convertToFloat (ds ++ 'e' : show e)
	foreign import primitive convertToFloat :: String -> Float

lexDigits :: ReadS String
lexDigits cs =
  case span isDigit cs of
    (ds@(_:_),cs') -> [(ds,cs')]
    ("",_) -> []
