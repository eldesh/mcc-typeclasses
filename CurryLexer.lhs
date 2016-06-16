% -*- LaTeX -*-
% $Id: CurryLexer.lhs 3221 2016-06-16 06:37:55Z wlux $
%
% Copyright (c) 1999-2015, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CurryLexer.lhs}
\section{A Lexer for Curry}
In this section a lexer for Curry is implemented.
\begin{verbatim}

> module CurryLexer(Token(..), Category(..), Attributes(..), Pragma(..),
>                   lexFile, lexer) where
> import LexComb
> import Position
> import Map
> import Char
> import List

\end{verbatim}
\paragraph{Tokens} Note that the equality and ordering instances of
\texttt{Token} disregard the attributes.
\begin{verbatim}

> data Token = Token Category Attributes

> instance Eq Token where
>   Token t1 _ == Token t2 _ = t1 == t2
> instance Ord Token where
>   Token t1 _ `compare` Token t2 _ = t1 `compare` t2

> data Category =
>   -- literals
>     CharTok | IntTok | RatTok | StringTok
>   -- identifiers
>   | Id | QId | Sym | QSym
>   -- punctuation symbols
>   | LeftParen | RightParen | Semicolon | LeftBrace | RightBrace
>   | LeftBracket | RightBracket | Comma | Underscore | Backquote
>   -- virtual punctation (inserted by layout)
>   | VSemicolon | VRightBrace
>   -- reserved identifiers
>   | KW_case | KW_class | KW_data | KW_default | KW_deriving | KW_do
>   | KW_else | KW_fcase | KW_foreign | KW_free | KW_if | KW_import | KW_in
>   | KW_infix | KW_infixl | KW_infixr | KW_instance | KW_let | KW_module
>   | KW_newtype | KW_of | KW_then | KW_type | KW_where
>   -- reserved operators
>   | At | Colon | DotDot | DoubleColon | Equals | Backslash | Bar
>   | LeftArrow | RightArrow | DoubleRightArrow | Tilde
>   -- special identifiers
>   | Id_as | Id_ccall | Id_forall | Id_hiding | Id_interface
>   | Id_primitive | Id_qualified | Id_rawcall | Id_safe | Id_unsafe
>   -- pragmas
>   | PragmaBegin Pragma | PragmaEnd
>   -- special operators
>   | Sym_Dot | Sym_Minus | Sym_Star
>   -- end-of-file token
>   | EOF
>   deriving (Eq,Ord)

> data Pragma =
>     ArityPragma | ClassPragma | DataPragma | HidingPragma | ModulePragma
>   | SuspectPragma | TrustPragma
>   deriving (Eq,Ord)

\end{verbatim}
There are different kinds of attributes associated with tokens.
Most attributes simply save the string corresponding to the token.
However, for qualified identifiers, we also record the list of module
qualifiers. The values corresponding to a literal token are properly
converted already. In order to simplify the creation and extraction of
attribute values we make use of records.
\begin{verbatim}

> data Attributes =
>     NoAttributes
>   | CharAttributes{ cval :: Char }
>   | IntAttributes{ ival :: Integer }
>   | RatAttributes{ rval :: Rational }
>   | StringAttributes{ sval :: String }
>   | IdentAttributes{ modul :: [String], sval :: String }

> instance Show Attributes where
>   showsPrec _ NoAttributes = showChar '_'
>   showsPrec _ (CharAttributes cval) = shows cval
>   showsPrec _ (IntAttributes ival) = shows ival
>   showsPrec _ (RatAttributes rval) = shows rval
>   showsPrec _ (StringAttributes sval) = shows sval
>   showsPrec _ (IdentAttributes mIdent ident) =
>     showString ("`" ++ concat (intersperse "." (mIdent ++ [ident])) ++ "'")

\end{verbatim}
The following functions can be used to construct tokens with
specific attributes.
\begin{verbatim}

> tok :: Category -> Token
> tok t = Token t NoAttributes

> idTok :: Category -> [String] -> String -> Token
> idTok t mIdent ident = Token t IdentAttributes{ modul = mIdent, sval = ident }

> charTok :: Char -> Token
> charTok c = Token CharTok CharAttributes{ cval = c }

> intTok :: Integer -> String -> Token
> intTok base digits =
>   Token IntTok IntAttributes{ ival = convertIntegral base digits }

> ratTok :: String -> String -> Int -> Token
> ratTok mant frac exp =
>   Token RatTok RatAttributes{ rval = convertFloat mant frac exp }

> stringTok :: String -> Token
> stringTok cs = Token StringTok StringAttributes{ sval = cs }

\end{verbatim}
The \texttt{Show} instance of \texttt{Token} is designed to display
all tokens in their source representation.
\begin{verbatim}

> instance Show Token where
>   showsPrec _ (Token Id a) = showString "identifier " . shows a
>   showsPrec _ (Token QId a) = showString "qualified identifier " . shows a
>   showsPrec _ (Token Sym a) = showString "operator " . shows a
>   showsPrec _ (Token QSym a) = showString "qualified operator " . shows a
>   showsPrec _ (Token IntTok a) = showString "integer " . shows a
>   showsPrec _ (Token RatTok a) = showString "rational " . shows a
>   showsPrec _ (Token CharTok a) = showString "character " . shows a
>   showsPrec _ (Token StringTok a) = showString "string " . shows a
>   showsPrec _ (Token LeftParen _) = showString "`('"
>   showsPrec _ (Token RightParen _) = showString "`)'"
>   showsPrec _ (Token Semicolon _) = showString "`;'"
>   showsPrec _ (Token LeftBrace _) = showString "`{'"
>   showsPrec _ (Token RightBrace _) = showString "`}'"
>   showsPrec _ (Token LeftBracket _) = showString "`['"
>   showsPrec _ (Token RightBracket _) = showString "`]'"
>   showsPrec _ (Token Comma _) = showString "`,'"
>   showsPrec _ (Token Underscore _) = showString "`_'"
>   showsPrec _ (Token Backquote _) = showString "``'"
>   showsPrec _ (Token VSemicolon _) =
>     showString "`;' (inserted due to layout)"
>   showsPrec _ (Token VRightBrace _) =
>     showString "`}' (inserted due to layout)"
>   showsPrec _ (Token At _) = showString "`@'"
>   showsPrec _ (Token Colon _) = showString "`:'"
>   showsPrec _ (Token DotDot _) = showString "`..'"
>   showsPrec _ (Token DoubleColon _) = showString "`::'"
>   showsPrec _ (Token Equals _) = showString "`='"
>   showsPrec _ (Token Backslash _) = showString "`\\'"
>   showsPrec _ (Token Bar _) = showString "`|'"
>   showsPrec _ (Token LeftArrow _) = showString "`<-'"
>   showsPrec _ (Token RightArrow _) = showString "`->'"
>   showsPrec _ (Token DoubleRightArrow _) = showString "`=>'"
>   showsPrec _ (Token Tilde _) = showString "`~'"
>   showsPrec _ (Token Sym_Dot _) = showString "operator `.'"
>   showsPrec _ (Token Sym_Minus _) = showString "operator `-'"
>   showsPrec _ (Token Sym_Star _) = showString "operator `*'"
>   showsPrec _ (Token KW_case _) = showString "`case'"
>   showsPrec _ (Token KW_class _) = showString "`class'"
>   showsPrec _ (Token KW_data _) = showString "`data'"
>   showsPrec _ (Token KW_default _) = showString "`default'"
>   showsPrec _ (Token KW_deriving _) = showString "`deriving'"
>   showsPrec _ (Token KW_do _) = showString "`do'"
>   showsPrec _ (Token KW_else _) = showString "`else'"
>   showsPrec _ (Token KW_fcase _) = showString "`fcase'"
>   showsPrec _ (Token KW_foreign _) = showString "`foreign'"
>   showsPrec _ (Token KW_free _) = showString "`free'"
>   showsPrec _ (Token KW_if _) = showString "`if'"
>   showsPrec _ (Token KW_import _) = showString "`import'"
>   showsPrec _ (Token KW_in _) = showString "`in'"
>   showsPrec _ (Token KW_infix _) = showString "`infix'"
>   showsPrec _ (Token KW_infixl _) = showString "`infixl'"
>   showsPrec _ (Token KW_infixr _) = showString "`infixr'"
>   showsPrec _ (Token KW_instance _) = showString "`instance'"
>   showsPrec _ (Token KW_let _) = showString "`let'"
>   showsPrec _ (Token KW_module _) = showString "`module'"
>   showsPrec _ (Token KW_newtype _) = showString "`newtype'"
>   showsPrec _ (Token KW_of _) = showString "`of'"
>   showsPrec _ (Token KW_then _) = showString "`then'"
>   showsPrec _ (Token KW_type _) = showString "`type'"
>   showsPrec _ (Token KW_where _) = showString "`where'"
>   showsPrec _ (Token Id_as _) = showString "identifier `as'"
>   showsPrec _ (Token Id_ccall _) = showString "identifier `ccall'"
>   showsPrec _ (Token Id_forall _) = showString "identifier `forall'"
>   showsPrec _ (Token Id_hiding _) = showString "identifier `hiding'"
>   showsPrec _ (Token Id_interface _) = showString "identifier `interface'"
>   showsPrec _ (Token Id_primitive _) = showString "identifier `primitive'"
>   showsPrec _ (Token Id_qualified _) = showString "identifier `qualified'"
>   showsPrec _ (Token Id_rawcall _) = showString "identifier `rawcall'"
>   showsPrec _ (Token Id_safe _) = showString "identifier `safe'"
>   showsPrec _ (Token Id_unsafe _) = showString "identifier `unsafe'"
>   showsPrec _ (Token (PragmaBegin p) _) =
>     showString "`{-# " . shows p . showString "'"
>   showsPrec _ (Token PragmaEnd _) = showString "`#-}'"
>   showsPrec _ (Token EOF _) = showString "<end-of-file>"

> instance Show Pragma where
>   showsPrec _ ArityPragma = showString "ARITY"
>   showsPrec _ ClassPragma = showString "CLASS"
>   showsPrec _ DataPragma = showString "DATA"
>   showsPrec _ HidingPragma = showString "HIDING"
>   showsPrec _ ModulePragma = showString "MODULE"
>   showsPrec _ SuspectPragma = showString "SUSPECT"
>   showsPrec _ TrustPragma = showString "TRUST"

\end{verbatim}
Tables for reserved operators, special identifiers, and supported
pragmas.
\begin{verbatim}

> reserved_ops, reserved_and_special_ops :: FM String Category
> reserved_ops = fromListFM [
>     ("@",  At),
>     (":",  Colon),
>     ("::", DoubleColon),
>     ("..", DotDot),
>     ("=",  Equals),
>     ("\\", Backslash),
>     ("|",  Bar),
>     ("<-", LeftArrow),
>     ("->", RightArrow),
>     ("=>", DoubleRightArrow),
>     ("~",  Tilde)
>   ]
> reserved_and_special_ops = foldr (uncurry addToFM) reserved_ops [
>     (".",  Sym_Dot),
>     ("-",  Sym_Minus),
>     ("*",  Sym_Star)
>   ]

> reserved_ids, reserved_and_special_ids :: FM String Category
> reserved_ids = fromListFM [
>     ("case",     KW_case),
>     ("class",    KW_class),
>     ("data",     KW_data),
>     ("default",  KW_default),
>     ("deriving", KW_deriving),
>     ("do",       KW_do),
>     ("else",     KW_else),
>     ("fcase",    KW_fcase),
>     ("foreign",  KW_foreign),
>     ("free",     KW_free),
>     ("if",       KW_if),
>     ("import",   KW_import),
>     ("in",       KW_in),
>     ("infix",    KW_infix),
>     ("infixl",   KW_infixl),
>     ("infixr",   KW_infixr),
>     ("instance", KW_instance),
>     ("let",      KW_let),
>     ("module",   KW_module),
>     ("newtype",  KW_newtype),
>     ("of",       KW_of),
>     ("then",     KW_then),
>     ("type",     KW_type),
>     ("where",    KW_where)
>   ]
> reserved_and_special_ids = foldr (uncurry addToFM) reserved_ids [
>     ("as",        Id_as),
>     ("ccall",     Id_ccall),
>     ("forall",    Id_forall),
>     ("hiding",    Id_hiding),
>     ("interface", Id_interface),
>     ("primitive", Id_primitive),
>     ("qualified", Id_qualified),
>     ("rawcall",   Id_rawcall),
>     ("safe",      Id_safe),
>     ("unsafe",    Id_unsafe)
>   ]

> pragma_keywords :: FM String Pragma
> pragma_keywords = fromListFM [
>     ("ARITY",   ArityPragma),
>     ("CLASS",   ClassPragma),
>     ("DATA",    DataPragma),
>     ("HIDING",  HidingPragma),
>     ("MODULE",  ModulePragma),
>     ("SUSPECT", SuspectPragma),
>     ("TRUST",   TrustPragma)
>   ]

\end{verbatim}
Character classes
\begin{verbatim}

> isIdent, isSym, isOctit, isHexit :: Char -> Bool
> isIdent c = isAlphaNum c || c `elem` "'_"
> isSym c = c `elem` "~!@#$%^&*+-=<>:?./|\\" {-$-}
> isOctit c = c >= '0' && c <= '7'
> isHexit c = isDigit c || c >= 'A' && c <= 'F' || c >= 'a' && c <= 'f'

\end{verbatim}
Lexing functions
\begin{verbatim}

> type SuccessL r = Position -> Token -> L r
> type FailL r = Position -> String -> L r

> lexFile :: L [(Position,Token)]
> lexFile = lexer tokens failL
>   where tokens p t@(Token c _)
>           | c == EOF = returnL [(p,t)]
>           | otherwise = lexFile `thenL` returnL . ((p,t):)

> lexer :: SuccessL r -> FailL r -> L r
> lexer success fail = skipBlanks
>   where -- skipBlanks moves past whitespace and comments
>         skipBlanks p [] bol = success p (tok EOF) p [] bol
>         skipBlanks p ('\t':cs) bol = skipBlanks (tab p) cs bol
>         skipBlanks p ('\n':cs) _ = skipBlanks (nl p) cs True
>         skipBlanks p ('-':'-':cs) _ =
>           skipBlanks (nl p) (drop 1 (dropWhile (/= '\n') cs)) True
>         skipBlanks p ('{':'-':'#':cs) bol =
>           (if bol then pragmaBOL p ('{':'-':'#':cs) else pragma)
>             (success p) (nestedComment p skipBlanks fail) (incr p 3) cs bol
>         skipBlanks p ('{':'-':cs) bol =
>           nestedComment p skipBlanks fail (incr p 2) cs bol
>         skipBlanks p (c:cs) bol
>           | isSpace c = skipBlanks (next p) cs bol
>           | otherwise =
>               (if bol then lexBOL else lexToken) success fail p (c:cs) bol

> nestedComment :: Position -> L r -> FailL r -> L r
> nestedComment p0 _ fail p [] =
>   fail p0 "Unterminated nested comment at end-of-file" p []
> nestedComment _ success _ p ('-':'}':cs) = success (incr p 2) cs
> nestedComment p0 success fail p ('{':'-':cs) =
>   nestedComment p (nestedComment p0 success fail) fail (incr p 2) cs
> nestedComment p0 success fail p ('\t':cs) =
>   nestedComment p0 success fail (tab p) cs
> nestedComment p0 success fail p ('\n':cs) =
>   nestedComment p0 success fail (nl p) cs
> nestedComment p0 success fail p (_:cs) =
>   nestedComment p0 success fail (next p) cs

\end{verbatim}
Lexing pragmas is a little bit complicated because lexically they
appear as nested comments using \verb|{-#| and \verb|#-}| as
delimiters. If \verb|{-#| is not followed by a known pragma keyword,
the lexer has to treat it as an opening delimiter of a nested comment
and skip input up to the matching \verb|-}| delimiter. On the other
hand, if a known pragma keyword is recognized, the usual layout
processing has to be applied, i.e., virtual closing braces and
semicolons may have to be inserted \emph{before} the
\texttt{PragmaBegin} token. This is achieved in the lexer
\texttt{pragmaBOL} by invoking the \texttt{pragma} lexer with a
success continuation that discards the \texttt{PragmaBegin} token and
returns the appropriate layout token instead. In addition, the lexer
backs up to the beginning of the pragma in that case so that
\verb|{-#| is analyzed again when the parser requests the next token.

\ToDo{Let the parsing combinators process layout instead of doing this
  in the lexer.}
\begin{verbatim}

> pragmaBOL :: Position -> String -> (Token -> L r) -> L r -> L r
> pragmaBOL _ _ success noPragma p cs _ [] =
>   pragma success noPragma p cs False []
> pragmaBOL p0 s0 success noPragma p cs _ ctxt@(n:_)
>   | col < n = pragma insertRightBrace noPragma p cs True ctxt
>   | col == n = pragma insertSemicolon noPragma p cs True ctxt
>   | otherwise =
>       pragma (\t p cs _ -> success t p cs False) noPragma p cs True ctxt
>   where col = column p0
>         insertRightBrace _ _ _ _ = success (tok VRightBrace) p0 s0 True
>         insertSemicolon _ _ _ _ = success (tok VSemicolon) p0 s0 False

> pragma :: (Token -> L r) -> L r -> L r
> pragma _ noPragma p [] = noPragma p []
> pragma success noPragma p (c:cs)
>   | c == '\t' = pragma success noPragma (tab p) cs
>   | c == '\n' = pragma success noPragma (nl p) cs
>   | isSpace c = pragma success noPragma (next p) cs
>   | isAlpha c =
>       maybe (noPragma (next p) cs)
>             (\t -> success (idTok (PragmaBegin t) [] ("{-# " ++ keyword))
>                            (incr p (length keyword)) rest)
>             (lookupFM keyword pragma_keywords)
>   | otherwise = noPragma p (c:cs)
>   where (keyword,rest) = span isIdent (c:cs)

> lexBOL :: SuccessL r -> FailL r -> L r
> lexBOL success fail p cs _ [] = lexToken success fail p cs False []
> lexBOL success fail p cs _ ctxt@(n:_)
>   | col < n = success p (tok VRightBrace) p cs True ctxt
>   | col == n = success p (tok VSemicolon) p cs False ctxt
>   | otherwise = lexToken success fail p cs False ctxt
>   where col = column p

> lexToken :: SuccessL r -> FailL r -> L r
> lexToken success fail p [] = success p (tok EOF) p []
> lexToken success fail p (c:cs)
>   | c == '(' = token LeftParen
>   | c == ')' = token RightParen
>   | c == ',' = token Comma
>   | c == ';' = token Semicolon
>   | c == '[' = token LeftBracket
>   | c == ']' = token RightBracket
>   | c == '_' = token Underscore
>   | c == '`' = token Backquote
>   | c == '{' = token LeftBrace
>   | c == '}' = token RightBrace
>   | c == '\'' = lexChar p (success p . charTok) fail (next p) cs
>   | c == '\"' = lexString p (success p . stringTok) fail (next p) cs
>   | isAlpha c = lexIdent (success p) p (c:cs)
>   | isSym c = lexSym (success p) p (c:cs)
>   | isDigit c = lexNumber (success p) p (c:cs)
>   | otherwise = fail p ("Illegal character " ++ show c) p cs
>   where token t = success p (tok t) (next p) cs

> lexIdent :: (Token -> L r) -> L r
> lexIdent cont p cs =
>   maybe (lexOptQual cont (token Id) [ident]) (cont . token)
>         (lookupFM ident reserved_and_special_ids)
>         (incr p (length ident)) rest
>   where (ident,rest) = span isIdent cs
>         token t = idTok t [] ident

> lexSym :: (Token -> L r) -> L r
> lexSym cont p cs
>   | "#-}" `isPrefixOf` cs =           -- 3 == length "#-}"
>       cont (idTok PragmaEnd [] "#-}") (incr p 3) (drop 3 cs)
>   | otherwise =
>       cont (token (maybe Sym id (lookupFM sym reserved_and_special_ops)))
>            (incr p (length sym)) rest
>   where (sym,rest) = span isSym cs
>         token t = idTok t [] sym

> lexOptQual :: (Token -> L r) -> Token -> [String] -> L r
> lexOptQual cont token mIdent p ('.':c:cs)
>   | isAlpha c = lexQualIdent cont identCont mIdent (next p) (c:cs)
>   | isSym c = lexQualSym cont identCont mIdent (next p) (c:cs)
>   where identCont _ _ = cont token p ('.':c:cs)
> lexOptQual cont token mIdent p cs = cont token p cs

> lexQualIdent :: (Token -> L r) -> L r -> [String] -> L r
> lexQualIdent cont identCont mIdent p cs =
>   maybe (lexOptQual cont (idTok QId mIdent ident) (mIdent ++ [ident]))
>         (const identCont)
>         (lookupFM ident reserved_ids)
>         (incr p (length ident)) rest
>   where (ident,rest) = span isIdent cs

> lexQualSym :: (Token -> L r) -> L r -> [String] -> L r
> lexQualSym cont identCont mIdent p cs =
>   maybe (cont (idTok QSym mIdent sym)) (const identCont)
>         (lookupFM sym reserved_ops)
>         (incr p (length sym)) rest
>   where (sym,rest) = span isSym cs

> lexNumber :: (Token -> L r) -> L r
> lexNumber cont p ('0':c:cs)
>   | c `elem` "oO" = lexNonDecimal 8 isOctit cont nullCont (incr p 2) cs
>   | c `elem` "xX" = lexNonDecimal 16 isHexit cont nullCont (incr p 2) cs
>   where nullCont _ _ = cont (intTok 10 "0") (next p) (c:cs)
> lexNumber cont p cs = lexOptFraction rat int p' rest
>   where p' = incr p (length digits)
>         (digits,rest) = span isDigit cs
>         int _ _ = cont (intTok 10 digits) p' rest
>         rat frac exp = cont (ratTok digits frac exp)

> lexNonDecimal :: Integer -> (Char -> Bool) -> (Token -> L r) -> L r -> L r
> lexNonDecimal base isDigit cont nullCont p cs
>   | null digits = nullCont p cs
>   | otherwise = cont (intTok base digits) (incr p (length digits)) rest
>   where (digits,rest) = span isDigit cs

> lexOptFraction :: (String -> Int -> L r) -> L r -> L r
> lexOptFraction cont noFrac p ('.':cs) = lexFraction cont noFrac (next p) cs
> lexOptFraction cont noFrac p cs = lexOptExponent (cont "") noFrac p cs

> lexFraction :: (String -> Int -> L r) -> L r -> L r
> lexFraction cont noFrac p cs
>   | null frac = noFrac p cs
>   | otherwise = lexOptExponent (cont frac) noExp p' rest
>   where p' = incr p (length frac)
>         (frac,rest) = span isDigit cs
>         noExp _ _ = cont frac 0 p' rest

> lexOptExponent :: (Int -> L r) -> L r -> L r
> lexOptExponent cont noExp p (c:cs)
>   | c `elem` "eE" = lexSignedExponent cont noExp (next p) cs
> lexOptExponent _ noExp p cs = noExp p cs

> lexSignedExponent :: (Int -> L r) -> L r -> L r
> lexSignedExponent cont noExp p ('+':cs) = lexExponent cont noExp (next p) cs
> lexSignedExponent cont noExp p ('-':cs) =
>   lexExponent (cont . negate) noExp (next p) cs
> lexSignedExponent cont noExp p cs = lexExponent cont noExp p cs

> lexExponent :: (Int -> L r) -> L r -> L r
> lexExponent cont noExp p cs
>   | null digits = noExp p cs
>   | otherwise = cont (convertIntegral 10 digits) (incr p (length digits)) rest
>   where (digits,rest) = span isDigit cs

> lexChar :: Position -> (Char -> L r) -> FailL r -> L r
> lexChar p0 success fail p [] = fail p0 "Illegal character constant" p []
> lexChar p0 success fail p (c:cs)
>   | c == '\\' = lexEscape p (lexCharChar p0 success fail) fail (next p) cs
>   | c == '\n' = fail p0 "Illegal character constant" p (c:cs)
>   | c == '\t' = lexCharChar p0 success fail c (tab p) cs
>   | otherwise = lexCharChar p0 success fail c (next p) cs

> lexCharChar :: Position -> (Char -> L r) -> FailL r -> Char -> L r
> lexCharChar p0 success fail c = lexCharEnd p0 (success c) fail

> lexCharEnd :: Position -> L r -> FailL r -> L r
> lexCharEnd _ success _ p ('\'':cs) = success (next p) cs
> lexCharEnd p0 _ fail p cs =
>   fail p0 "Improperly terminated character constant" p cs

> lexString :: Position -> (String -> L r) -> FailL r -> L r
> lexString p0 _ fail p [] =
>   fail p0 "Improperly terminated string constant" p []
> lexString p0 success fail p (c:cs)
>   | c == '\\' = lexStringEscape p0 p success fail (next p) cs
>   | c == '\"' = success "" (next p) cs
>   | c == '\n' = fail p0 "Improperly terminated string constant" p (c:cs)
>   | c == '\t' = lexStringChar p0 success fail c (tab p) cs
>   | otherwise = lexStringChar p0 success fail c (next p) cs

> lexStringChar :: Position -> (String -> L r) -> FailL r -> Char -> L r
> lexStringChar p0 success fail c = lexString p0 (success . (c:)) fail

> lexStringEscape :: Position -> Position -> (String -> L r) -> FailL r -> L r
> lexStringEscape _ p1 _ fail p [] = lexEscape p1 undefined fail p []
> lexStringEscape p0 p1 success fail p (c:cs)
>   | c == '&' = lexString p0 success fail (next p) cs
>   | isSpace c = lexStringGap (lexString p0 success fail) fail p (c:cs)
>   | otherwise = lexEscape p1 (lexStringChar p0 success fail) fail p (c:cs)

> lexStringGap :: L r -> FailL r -> L r
> lexStringGap _ fail p [] = fail p "End of file in string gap" p []
> lexStringGap success fail p (c:cs)
>   | c == '\\' = success (next p) cs
>   | c == '\t' = lexStringGap success fail (tab p) cs
>   | c == '\n' = lexStringGap success fail (nl p) cs
>   | isSpace c = lexStringGap success fail (next p) cs
>   | otherwise = fail p ("Illegal character in string gap " ++ show c) p (c:cs)

> lexEscape :: Position -> (Char -> L r) -> FailL r -> L r
> lexEscape _ success _ p ('a':cs) = success '\a' (next p) cs
> lexEscape _ success _ p ('b':cs) = success '\b' (next p) cs
> lexEscape _ success _ p ('f':cs) = success '\f' (next p) cs
> lexEscape _ success _ p ('n':cs) = success '\n' (next p) cs
> lexEscape _ success _ p ('r':cs) = success '\r' (next p) cs
> lexEscape _ success _ p ('t':cs) = success '\t' (next p) cs
> lexEscape _ success _ p ('v':cs) = success '\v' (next p) cs
> lexEscape _ success _ p ('\\':cs) = success '\\' (next p) cs
> lexEscape _ success _ p ('\"':cs) = success '\"' (next p) cs
> lexEscape _ success _ p ('\'':cs) = success '\'' (next p) cs
> lexEscape _ success _ p ('^':c:cs)
>   | isUpper c || c `elem` "@[\\]^_" =
>       success (chr (ord c `mod` 32)) (incr p 2) cs
> lexEscape p0 success fail p ('o':c:cs)
>   | isOctit c = numEscape 8 isOctit p0 success fail (next p) (c:cs)
> lexEscape p0 success fail p ('x':c:cs)
>   | isHexit c = numEscape 16 isHexit p0 success fail (next p) (c:cs)
> lexEscape p0 success fail p (c:cs)
>   | isDigit c = numEscape 10 isDigit p0 success fail p (c:cs)
> lexEscape p0 success fail p cs = asciiEscape p0 success fail p cs

> asciiEscape :: Position -> (Char -> L r) -> FailL r -> L r
> asciiEscape _ success _ p ('N':'U':'L':cs) = success '\NUL' (incr p 3) cs
> asciiEscape _ success _ p ('S':'O':'H':cs) = success '\SOH' (incr p 3) cs
> asciiEscape _ success _ p ('S':'T':'X':cs) = success '\STX' (incr p 3) cs
> asciiEscape _ success _ p ('E':'T':'X':cs) = success '\ETX' (incr p 3) cs
> asciiEscape _ success _ p ('E':'O':'T':cs) = success '\EOT' (incr p 3) cs
> asciiEscape _ success _ p ('E':'N':'Q':cs) = success '\ENQ' (incr p 3) cs
> asciiEscape _ success _ p ('A':'C':'K':cs) = success '\ACK' (incr p 3) cs 
> asciiEscape _ success _ p ('B':'E':'L':cs) = success '\BEL' (incr p 3) cs
> asciiEscape _ success _ p ('B':'S':cs) = success '\BS' (incr p 2) cs
> asciiEscape _ success _ p ('H':'T':cs) = success '\HT' (incr p 2) cs
> asciiEscape _ success _ p ('L':'F':cs) = success '\LF' (incr p 2) cs
> asciiEscape _ success _ p ('V':'T':cs) = success '\VT' (incr p 2) cs
> asciiEscape _ success _ p ('F':'F':cs) = success '\FF' (incr p 2) cs
> asciiEscape _ success _ p ('C':'R':cs) = success '\CR' (incr p 2) cs
> asciiEscape _ success _ p ('S':'O':cs) = success '\SO' (incr p 2) cs
> asciiEscape _ success _ p ('S':'I':cs) = success '\SI' (incr p 2) cs
> asciiEscape _ success _ p ('D':'L':'E':cs) = success '\DLE' (incr p 3) cs 
> asciiEscape _ success _ p ('D':'C':'1':cs) = success '\DC1' (incr p 3) cs
> asciiEscape _ success _ p ('D':'C':'2':cs) = success '\DC2' (incr p 3) cs
> asciiEscape _ success _ p ('D':'C':'3':cs) = success '\DC3' (incr p 3) cs
> asciiEscape _ success _ p ('D':'C':'4':cs) = success '\DC4' (incr p 3) cs
> asciiEscape _ success _ p ('N':'A':'K':cs) = success '\NAK' (incr p 3) cs
> asciiEscape _ success _ p ('S':'Y':'N':cs) = success '\SYN' (incr p 3) cs
> asciiEscape _ success _ p ('E':'T':'B':cs) = success '\ETB' (incr p 3) cs
> asciiEscape _ success _ p ('C':'A':'N':cs) = success '\CAN' (incr p 3) cs 
> asciiEscape _ success _ p ('E':'M':cs) = success '\EM' (incr p 2) cs
> asciiEscape _ success _ p ('S':'U':'B':cs) = success '\SUB' (incr p 3) cs
> asciiEscape _ success _ p ('E':'S':'C':cs) = success '\ESC' (incr p 3) cs
> asciiEscape _ success _ p ('F':'S':cs) = success '\FS' (incr p 2) cs
> asciiEscape _ success _ p ('G':'S':cs) = success '\GS' (incr p 2) cs
> asciiEscape _ success _ p ('R':'S':cs) = success '\RS' (incr p 2) cs
> asciiEscape _ success _ p ('U':'S':cs) = success '\US' (incr p 2) cs
> asciiEscape _ success _ p ('S':'P':cs) = success '\SP' (incr p 2) cs
> asciiEscape _ success _ p ('D':'E':'L':cs) = success '\DEL' (incr p 3) cs
> asciiEscape p0 _ fail p cs = fail p0 "Illegal escape sequence" p cs

\end{verbatim}
The \texttt{numEscape} lexer accepts character codes in the character
range supported by the Haskell compiler. Note that hbc and nhc98 up to
(at least) version 1.18 report \texttt{(maxBound::Char) == 255}, even
though they actually support a larger character set range.
\begin{verbatim}

> numEscape :: Int -> (Char -> Bool) -> Position -> (Char -> L r) -> FailL r
>           -> L r
> numEscape base isDigit p0 success fail p cs
>   | n >= min && n <= max = success (chr n) (incr p (length digits)) rest
>   | otherwise = fail p0 "Numeric escape out-of-range" p cs
>   where (digits,rest) = span isDigit cs
>         n = convertIntegral base digits
>         min = ord minBound
>         max = ord maxBound

\end{verbatim}
