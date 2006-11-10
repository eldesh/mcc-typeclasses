-- $Id: Read.curry 1997 2006-11-10 20:45:06Z wlux $
--
-- Copyright (c) 2004-2006, Wolfgang Lux
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
readInt = read (Numeric.readSigned Numeric.readDec)
readHex = read Numeric.readHex

readFloat :: String -> Float
readFloat = read (Numeric.readSigned Numeric.readFloat)
