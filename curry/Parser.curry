-- $Id: Parser.curry 3273 2016-07-13 21:23:01Z wlux $
-- 
-- Copyright (c) 2004-2016, Wolfgang Lux
-- See ../LICENSE for the full license.

-- Functional logic parsing combinators based on
-- Rafael Caballero, Francisco J. López-Fraguas. A Functional-Logic
-- Perspective on Parsing. In: Proc. FLOPS'99, Springer LNCS 1722,
-- pp. 85-99.

-- This implementation avoids a quadratic time complexity problem
-- present in the original implementation and can therefore be used
-- for large input strings.

module Parser where

import Char
import List

infixr 4 <*>
infixr 3 >>>
infixr 2 <|>, <||>

-- basic parsing combinators
type Parser s = [s] -> [s]

empty :: Parser s
empty s = s

terminal :: a -> Parser a
terminal t (t':ts) | t =:= t' = ts

-- NB Don't try to simplify the fcase expression below. It ensures
--    that p1 is evaluated before p2. In contrast to the original
--    implementation from the paper
--      (p1 <*> p2) ts | p1 ts =:= ts' = p2 ts' where ts' free
--    this implementation does not evaluate the remaining input list
--    to normal form and therefore does not suffer from a quadratic
--    time complexity in the length of the input list.
(<*>) :: Parser a -> Parser a -> Parser a
(p1 <*> p2) ts =
  fcase p1 ts of
    ts@[] -> p2 ts
    ts@(_:_) -> p2 ts

(<|>) :: Parser a -> Parser a -> Parser a
(p <|> _) ts = p ts
(_ <|> q) ts = q ts

-- parsing combinator with representation
type ParserRep a s = a -> Parser s

satisfy :: (a -> Bool) -> ParserRep a a
satisfy p t (t':ts) | t =:= t' &> p t = ts

(<||>) :: ParserRep a b -> ParserRep a b -> ParserRep a b
(p1 <||> p2) rep = p1 rep <|> p2 rep

-- NB (>>>) is called (>>) in the paper, but was renamed in order
--    to avoid a conflict with the monadic (>>) operator.
--    Don't try to simplify the fcase expression below. It serves
--    the same purpose as in (<*>) and avoids the quadratic time
--    complexity entailed by the first unification in the original
--    implementation:
--      (p >>> e) r ts | solve (p ts =:= ts') &> e =:= r = ts' where ts' free
(>>>) :: Parser a -> b -> ParserRep b a
(p >>> e) r ts =
  fcase p ts of
    ts@[] | e =:= r -> ts
    ts@(_:_) | e =:= r -> ts

-- NB Compared to the paper, some and star have been eta-expanded to
--    avoid sharing the free variables between applications of parser p.
some, star :: ParserRep a b -> ParserRep [a] b
some p rep = (p x <*> star p xs >>> x:xs) rep where x, xs free
star p rep = some p rep
         <|> (empty >>> []) rep

-- invoking parsers
-- NB these functions were not defined in the paper
parse :: Parser a -> [a] -> Bool
parse p ts = p ts =:= []

parseRep :: ParserRep a b -> [b] -> a
parseRep p ts | parse (p r) ts = r
  where r free

parseOne :: ParserRep a b -> [b] -> a
parseOne p ts = head $ findall (\r -> parse (p r) ts)
