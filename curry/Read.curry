-- $Id: Read.curry 1744 2005-08-23 16:17:12Z wlux $
--
-- Copyright (c) 2004-2005, Wolfgang Lux
-- See ../LICENSE for the full license.

module Read(Read.readInt, Read.readNat, Read.readHex, Read.readFloat) where
import Char
import Numeric
import Success

type ReadS a = String -> [(a,String)]

read :: ReadS a -> String -> a
read r cs = choose [x | (x,cs') <-  r (dropWhile isSpace cs), all isSpace cs']

readNat, readInt, readHex :: String -> Int
readNat = read Numeric.readDec
readInt = read (Numeric.readSignedInt Numeric.readDec)
readHex = read Numeric.readHex

readFloat :: String -> Float
readFloat = read (Numeric.readSignedFloat Numeric.readFloat)
