-- $Id: Char.curry 2028 2006-11-28 09:05:38Z wlux $
--
-- Copyright (c) 2002-2006, Wolfgang Lux
-- See ../LICENSE for the full license.

module Char(module Char, ord, chr) where

{- To do: Unicode support -}

isAscii c = c <= '\x80'
isLatin1 c = c <= '\xff'
isControl c = c < ' ' || c >= '\DEL' && c <= '\x9f'
isPrint c = not (isControl c)
isSpace c = c `elem` " \t\n\r\f\v\xa0"
isUpper c = c >= 'A' && c <= 'Z'
isLower c = c >= 'a' && c <= 'z'
isAlpha c = isLower c || isUpper c
isDigit c = c >= '0' && c <= '9'
isOctDigit c = c >= '0' && c <= '7'
isHexDigit c = isDigit c || c >= 'a' && c <= 'f' || c >= 'A' && c <= 'F'
isAlphaNum c = isAlpha c || isDigit c

toLower c = if isUpper c then chr (ord c - ord 'A' + ord 'a') else c
toUpper c = if isLower c then chr (ord c - ord 'a' + ord 'A') else c

digitToInt c
  | isDigit c = ord c - ord '0'
  | c >= 'a' && c <= 'f' = ord c - ord 'a' + 10
  | c >= 'A' && c <= 'F' = ord c - ord 'A' + 10

intToDigit i
  | i >= 0 && i < 10 = chr (i + ord '0')
  | i >= 10 && i < 16 = chr (i - 10 + ord 'a')
