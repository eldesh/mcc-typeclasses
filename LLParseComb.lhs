% -*- LaTeX -*-
% $Id: LLParseComb.lhs 3221 2016-06-16 06:37:55Z wlux $
%
% Copyright (c) 1999-2015, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{LLParseComb.lhs}
\section{Parsing Combinators}\label{sec:ll-parsecomb}
The parsing combinators implemented in the module \texttt{LLParseComb}
are based on the LL(1) parsing combinators developed by Swierstra and
Duponcheel~\cite{SwierstraDuponcheel96:Parsers}. They have been
adapted to using continuation passing style in order to work with the
lexing combinators described in the previous section. In addition, the
facilities for error correction are omitted in this implementation.

The two functions \texttt{applyParser} and \texttt{prefixParser} use
the specified parser for parsing a string. When \texttt{applyParser}
is used, an error is reported if the parser does not consume the whole
string, whereas \texttt{prefixParser} discards the rest of the input
string in this case.
\begin{verbatim}

> module LLParseComb(Symbol(..),Parser,
>                    applyParser,prefixParser, position,succeed,symbol,
>                    (<?>),(<|>),(<|?>),(<*>),(<\>),(<\\>),
>                    opt,(<$>),(<$->),(<*->),(<-*>),(<**>),(<?*>),(<**?>),(<.>),
>                    many,many1, sepBy,sepBy1, chainr,chainr1,chainl,chainl1,
>                    bracket,ops, layoutOn,layoutOff,layoutEnd) where
> import Prelude hiding(lex)
> import Position
> import Set
> import Map
> import Maybe
> import Monad
> import Error
> import LexComb

> infixl 5 <\>, <\\>
> infixl 4 <*>, <$>, <$->, <*->, <-*>, <**>, <?*>, <**?>, <.>
> infixl 3 <|>, <|?>
> infixl 2 <?>, `opt`

\end{verbatim}
\paragraph{Parser types}
\begin{verbatim}

> class (Ord s,Show s) => Symbol s where
>   isEOF :: s -> Bool

> type SuccessCont r s = Position -> s -> L r
> type FailureCont r = Position -> String -> L r
> type Lexer r s = SuccessCont r s -> FailureCont r -> L r
> type ParseFun r s a = (a -> SuccessCont r s) -> FailureCont r
>                     -> SuccessCont r s

> data Parser r s a = Parser (Maybe (ParseFun r s a))
>                            (FM s (Lexer r s -> ParseFun r s a))

> instance Symbol s => Show (Parser r s a) where
>   showsPrec p (Parser e ps) = showParen (p >= 10) $                      -- $
>     showString "Parser " . shows (isJust e) .
>     showChar ' ' . shows (domainFM ps)

> applyParser :: Symbol s => Parser r s r -> Lexer r s -> FilePath -> String
>             -> Error r
> applyParser p lexer = lex (lexer (choose p lexer done failL) failL)
>   where done x pos s
>           | isEOF s = returnL x
>           | otherwise = failL pos (unexpected s)

> prefixParser :: Symbol s => Parser r s r -> Lexer r s -> FilePath -> String
>              -> Error r
> prefixParser p lexer = lex (lexer (choose p lexer discard failL) failL)
>   where discard x _ _ = returnL x

> choose :: Symbol s => Parser r s a -> Lexer r s -> ParseFun r s a
> choose (Parser e ps) lexer success fail pos s =
>   case lookupFM s ps of
>     Just p -> p lexer success fail pos s
>     Nothing ->
>       case e of
>         Just p -> p success fail pos s
>         Nothing -> fail pos (unexpected s)

> unexpected :: Symbol s => s -> String
> unexpected s
>   | isEOF s = "Unexpected end-of-file"
>   | otherwise = "Unexpected token " ++ show s

\end{verbatim}
\paragraph{Basic combinators}
\begin{verbatim}

> position :: Symbol s => Parser r s Position
> position = Parser (Just p) zeroFM
>   where p success _ pos = success pos pos

> succeed :: Symbol s => a -> Parser r s a
> succeed x = Parser (Just p) zeroFM
>   where p success _ = success x

> symbol :: Symbol s => s -> Parser r s s
> symbol s = Parser Nothing (addToFM s p zeroFM)
>   where p lexer success fail _ s = lexer (success s) fail

> (<?>) :: Symbol s => Parser r s a -> String -> Parser r s a
> p <?> msg = p <|> Parser (Just pfail) zeroFM
>   where pfail _ fail pos _ = fail pos msg

> (<|>) :: Symbol s => Parser r s a -> Parser r s a -> Parser r s a
> Parser e1 ps1 <|> Parser e2 ps2
>   | isJust e1 && isJust e2 = error "Ambiguous parser for empty word"
>   | not (nullSet common) = error ("Ambiguous parser for " ++ show common)
>   | otherwise = Parser (e1 `mplus` e2) (insertIntoFM ps1 ps2)
>   where common = domainFM ps1 `intersectionSet` domainFM ps2

\end{verbatim}
The parsing combinators presented so far require that the grammar
being parsed is LL(1). In some cases it may be difficult or even
impossible to transform a grammar into LL(1) form. As a remedy, we
include a non-deterministic version of the choice combinator in
addition to the deterministic combinator adapted from the paper. For
every symbol from the intersection of the parser's first sets, the
combinator \texttt{(<|?>)} applies both parsing functions to the input
stream and uses that one which processes the longer prefix of the
input stream irrespective of whether it succeeds or fails. If both
functions recognize the same prefix, we choose the one that succeeds
and report an ambiguous parse error if both succeed.
\begin{verbatim}

> (<|?>) :: Symbol s => Parser r s a -> Parser r s a -> Parser r s a
> Parser e1 ps1 <|?> Parser e2 ps2
>   | isJust e1 && isJust e2 = error "Ambiguous parser for empty word"
>   | otherwise = Parser (e1 `mplus` e2) (insertIntoFM ps1' ps2)
>   where ps1' = fromListFM [(s,maybe p (try p) (lookupFM s ps2))
>                           | (s,p) <- toListFM ps1]
>         try p1 p2 lexer success fail pos s =
>           closeL1 p2s `thenL` \p2s' ->
>           closeL1 p2f `thenL` \p2f' ->
>           parse p1 (retry p2s') (retry p2f')
>           where p2s r1 = parse p2 (select True r1) (select False r1)
>                 p2f r1 = parse p2 (flip (select False) r1) (select False r1)
>                 parse p psucc pfail =
>                   p lexer (successK psucc) (failK pfail) pos s
>                 successK k x pos s = k (pos,success x pos s)
>                 failK k pos msg = k (pos,fail pos msg)
>                 retry k (pos,p) = closeL0 p `thenL` curry k pos
>         select suc (pos1,p1) (pos2,p2) =
>           case pos1 `compare` pos2 of
>             GT -> p1
>             EQ
>               | suc -> error ("Ambiguous parse before " ++ show pos1)
>               | otherwise -> p1
>             LT -> p2

> (<*>) :: Symbol s => Parser r s (a -> b) -> Parser r s a -> Parser r s b
> Parser (Just p1) ps1 <*> ~p2@(Parser e2 ps2) =
>   Parser (fmap (seqEE p1) e2)
>          (insertIntoFM (fmap (flip seqPP p2) ps1) (fmap (seqEP p1) ps2))
> Parser Nothing ps1 <*> p2 = Parser Nothing (fmap (flip seqPP p2) ps1)

> seqEE :: Symbol s => ParseFun r s (a -> b) -> ParseFun r s a
>       -> ParseFun r s b
> seqEE p1 p2 success fail = p1 (\f -> p2 (success . f) fail) fail

> seqEP :: Symbol s => ParseFun r s (a -> b) -> (Lexer r s -> ParseFun r s a)
>       -> Lexer r s -> ParseFun r s b
> seqEP p1 p2 lexer success fail = p1 (\f -> p2 lexer (success . f) fail) fail

> seqPP :: Symbol s => (Lexer r s -> ParseFun r s (a -> b)) -> Parser r s a
>       -> Lexer r s -> ParseFun r s b
> seqPP p1 p2 lexer success fail =
>   p1 lexer (\f -> choose p2 lexer (success . f) fail) fail

> insertIntoFM :: Ord a => FM a b -> FM a b -> FM a b
> insertIntoFM map1 map2 = foldr (uncurry addToFM) map2 (toListFM map1)

\end{verbatim}
The combinators \verb|<\\>| and \verb|<\>| can be used to restrict
the first set of a parser. This is useful for combining two parsers
with an overlapping first set with the deterministic combinator <|>.
\begin{verbatim}

> (<\>) :: Symbol s => Parser r s a -> Parser r s b -> Parser r s a
> p <\> Parser _ ps = p <\\> map fst (toListFM ps)

> (<\\>) :: Symbol s => Parser r s a -> [s] -> Parser r s a
> Parser e ps <\\> xs = Parser e (foldr deleteFromFM ps xs)

\end{verbatim}
\paragraph{Other combinators.}
Note that some of these combinators have not been published in the
paper, but were taken from the implementation found on the web.
\begin{verbatim}

> opt :: Symbol s => Parser r s a -> a -> Parser r s a
> p `opt` x = p <|> succeed x

> (<$>) :: Symbol s => (a -> b) -> Parser r s a -> Parser r s b
> f <$> p = succeed f <*> p

> (<$->) :: Symbol s => a -> Parser r s b -> Parser r s a
> f <$-> p = const f <$> p {-$-}

> (<*->) :: Symbol s => Parser r s a -> Parser r s b -> Parser r s a
> p <*-> q = const <$> p <*> q {-$-}

> (<-*>) :: Symbol s => Parser r s a -> Parser r s b -> Parser r s b
> p <-*> q = const id <$> p <*> q {-$-}

> (<**>) :: Symbol s => Parser r s a -> Parser r s (a -> b) -> Parser r s b
> p <**> q = flip ($) <$> p <*> q

> (<?*>) :: Symbol s => Parser r s (a -> a) -> Parser r s a -> Parser r s a
> p <?*> q = (p `opt` id) <*> q

> (<**?>) :: Symbol s => Parser r s a -> Parser r s (a -> a) -> Parser r s a
> p <**?> q = p <**> (q `opt` id)

> (<.>) :: Symbol s => Parser r s (a -> b) -> Parser r s (b -> c)
>       -> Parser r s (a -> c)
> p <.> q = p <**> ((.) <$> q)

> many :: Symbol s => Parser r s a -> Parser r s [a]
> many p = many1 p `opt` []

> many1 :: Symbol s => Parser r s a -> Parser r s [a]
> -- many1 p = (:) <$> p <*> many p
> many1 p = (:) <$> p <*> (many1 p `opt` [])

\end{verbatim}
The first definition of \texttt{many1} is commented out because it
does not compile under nhc. This is due to a -- known -- bug in the
type checker of nhc which expects a default declaration when compiling
mutually recursive functions with class constraints. However, no such
default can be given in the above case because neither of the types
involved is a numeric type.
\begin{verbatim}

> sepBy :: Symbol s => Parser r s a -> Parser r s b -> Parser r s [a]
> p `sepBy` q = p `sepBy1` q `opt` []

> sepBy1 :: Symbol s => Parser r s a -> Parser r s b -> Parser r s [a]
> p `sepBy1` q = (:) <$> p <*> many (q <-*> p) {-$-}

> chainr :: Symbol s => Parser r s a -> Parser r s (a -> a -> a) -> a
>        -> Parser r s a
> chainr p op x = chainr1 p op `opt` x

> chainr1 :: Symbol s => Parser r s a -> Parser r s (a -> a -> a)
>         -> Parser r s a
> chainr1 p op = r
>   where r = p <**> (flip <$> op <*> r `opt` id) {-$-}

> chainl :: Symbol s => Parser r s a -> Parser r s (a -> a -> a) -> a
>        -> Parser r s a
> chainl p op x = chainl1 p op `opt` x

> chainl1 :: Symbol s => Parser r s a -> Parser r s (a -> a -> a)
>         -> Parser r s a
> chainl1 p op = foldF <$> p <*> many (flip <$> op <*> p)
>   where foldF x [] = x
>         foldF x (f:fs) = foldF (f x) fs

> bracket :: Symbol s => Parser r s a -> Parser r s b -> Parser r s a
>         -> Parser r s b
> bracket open p close = open <-*> p <*-> close

> ops :: Symbol s => [(s,a)] -> Parser r s a
> ops [] = error "internal error: ops"
> ops [(s,x)] = x <$-> symbol s
> ops ((s,x):rest) = x <$-> symbol s <|> ops rest

\end{verbatim}
\paragraph{Layout combinators}
Note that the layout functions grab the next token (and its position).
After modifying the layout context, the continuation is called with
the same token and an undefined result.
\begin{verbatim}

> layoutOn :: Symbol s => Parser r s a
> layoutOn = Parser (Just on) zeroFM
>   where on success _ pos = pushContext (column pos) . success undefined pos

> layoutOff :: Symbol s => Parser r s a
> layoutOff = Parser (Just off) zeroFM
>   where off success _ pos = pushContext (-1) . success undefined pos

> layoutEnd :: Symbol s => Parser r s a
> layoutEnd = Parser (Just end) zeroFM
>   where end success _ pos = popContext . success undefined pos

\end{verbatim}
