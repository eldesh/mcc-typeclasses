% -*- LaTeX -*-
% $Id: CurryLexer.lhs 2088 2007-02-05 09:27:49Z wlux $
%
% Copyright (c) 1999-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CurryLexer.lhs}
\section{A Lexer for Curry}
In this section a lexer for Curry is implemented.
\begin{verbatim}

> module CurryLexer where
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
>     CharTok | IntTok | FloatTok | StringTok
>   -- identifiers
>   | Id | QId | Sym | QSym
>   -- punctuation symbols
>   | LeftParen | RightParen | Semicolon | LeftBrace | RightBrace
>   | LeftBracket | RightBracket | Comma | Underscore | Backquote
>   -- virtual punctation (inserted by layout)
>   | VSemicolon | VRightBrace
>   -- reserved identifiers
>   | KW_case | KW_class | KW_data | KW_deriving | KW_do | KW_else
>   | KW_foreign | KW_free | KW_if | KW_import | KW_in | KW_infix
>   | KW_infixl | KW_infixr | KW_instance | KW_let | KW_module
>   | KW_newtype | KW_of | KW_then | KW_type | KW_where
>   -- reserved operators
>   | At | Colon | DotDot | DoubleColon | Equals | Backslash | Bar
>   | LeftArrow | RightArrow | DoubleRightArrow | Tilde
>   -- special identifiers
>   | Id_as | Id_ccall | Id_forall | Id_hiding | Id_interface
>   | Id_primitive | Id_qualified | Id_safe | Id_unsafe
>   -- pragmas
>   | PragmaBegin Pragma | PragmaEnd
>   -- special operators
>   | Sym_Dot | Sym_Minus | Sym_Star
>   -- end-of-file token
>   | EOF
>   deriving (Eq,Ord)

> data Pragma = SuspectPragma | TrustPragma deriving (Eq,Ord)

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
>   | IntAttributes{ ival :: Int }
>   | FloatAttributes{ fval :: Double }
>   | StringAttributes{ sval :: String }
>   | IdentAttributes{ modul :: [String], sval :: String }

> instance Show Attributes where
>   showsPrec _ NoAttributes = showChar '_'
>   showsPrec _ (CharAttributes cval) = shows cval
>   showsPrec _ (IntAttributes ival) = shows ival
>   showsPrec _ (FloatAttributes fval) = shows fval
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

> intTok :: Int -> String -> Token
> intTok base digits =
>   Token IntTok IntAttributes{ ival = convertIntegral base digits }

> floatTok :: String -> String -> Int -> Token
> floatTok mant frac exp =
>   Token FloatTok FloatAttributes{ fval = convertFloating mant frac exp }

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
>   showsPrec _ (Token FloatTok a) = showString "float " . shows a
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
>   showsPrec _ (Token KW_deriving _) = showString "`deriving'"
>   showsPrec _ (Token KW_do _) = showString "`do'"
>   showsPrec _ (Token KW_else _) = showString "`else'"
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
>   showsPrec _ (Token Id_safe _) = showString "identifier `safe'"
>   showsPrec _ (Token Id_unsafe _) = showString "identifier `unsafe'"
>   showsPrec _ (Token (PragmaBegin _) a) = shows a
>   showsPrec _ (Token PragmaEnd _) = showString "`#-}'"
>   showsPrec _ (Token EOF _) = showString "<end-of-file>"

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
>     ("deriving", KW_deriving),
>     ("do",       KW_do),
>     ("else",     KW_else),
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
>     ("safe",      Id_safe),
>     ("unsafe",    Id_unsafe)
>   ]

> pragma_keywords :: FM String Pragma
> pragma_keywords = fromListFM [
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

> type SuccessL a = Position -> Token -> L a
> type FailL a = Position -> String -> L a

> lexFile :: L [(Position,Token)]
> lexFile = lexer tokens failL
>   where tokens p t@(Token c _)
>           | c == EOF = returnL [(p,t)]
>           | otherwise = lexFile `thenL` returnL . ((p,t):)

> lexer :: SuccessL a -> FailL a -> L a
> lexer success fail = skipBlanks
>   where -- skipBlanks moves past whitespace and comments
>         skipBlanks p [] bol = success p (tok EOF) p [] bol
>         skipBlanks p ('\t':s) bol = skipBlanks (tab p) s bol
>         skipBlanks p ('\n':s) _ = skipBlanks (nl p) s True
>         skipBlanks p ('-':'-':s) _ =
>           skipBlanks (nl p) (tail' (dropWhile (/= '\n') s)) True
>         skipBlanks p ('{':'-':'#':s) bol =
>           (if bol then pragmaBOL p ('{':'-':'#':s) else pragma)
>             (success p) (nestedComment p skipBlanks fail) (incr p 3) s bol
>         skipBlanks p ('{':'-':s) bol =
>           nestedComment p skipBlanks fail (incr p 2) s bol
>         skipBlanks p (c:s) bol
>           | isSpace c = skipBlanks (next p) s bol
>           | otherwise =
>               (if bol then lexBOL else lexToken) success fail p (c:s) bol
>         tail' [] = []
>         tail' (_:tl) = tl

> nestedComment :: Position -> L a -> FailL a -> L a
> nestedComment p0 _ fail p [] =
>   fail p0 "Unterminated nested comment at end-of-file" p []
> nestedComment _ success _ p ('-':'}':s) = success (incr p 2) s
> nestedComment p0 success fail p ('{':'-':s) =
>   nestedComment p (nestedComment p0 success fail) fail (incr p 2) s
> nestedComment p0 success fail p ('\t':s) =
>   nestedComment p0 success fail (tab p) s
> nestedComment p0 success fail p ('\n':s) =
>   nestedComment p0 success fail (nl p) s
> nestedComment p0 success fail p (_:s) =
>   nestedComment p0 success fail (next p) s

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

> pragmaBOL :: Position -> String -> (Token -> L a) -> L a -> L a
> pragmaBOL _ _ success noPragma p s _ [] = pragma success noPragma p s False []
> pragmaBOL p0 s0 success noPragma p s _ ctxt@(n:rest)
>   | col < n = pragma insertRightBrace noPragma p s True ctxt
>   | col == n = pragma insertSemicolon noPragma p s True ctxt
>   | otherwise =
>       pragma (\t p s _ -> success t p s False) noPragma p s True ctxt
>   where col = column p0
>         insertRightBrace _ _ _ _ _ = success (tok VRightBrace) p0 s0 True rest
>         insertSemicolon _ _ _ _ = success (tok VSemicolon) p0 s0 False

> pragma :: (Token -> L a) -> L a -> L a
> pragma _ noPragma p [] = noPragma p []
> pragma success noPragma p (c:s)
>   | c == '\t' = pragma success noPragma (tab p) s
>   | c == '\n' = pragma success noPragma (nl p) s
>   | isSpace c = pragma success noPragma (next p) s
>   | isAlpha c =
>       maybe (noPragma (next p) s)
>             (\t -> success (idTok (PragmaBegin t) [] ("{-# " ++ keyword))
>                            (incr p (length keyword)) rest)
>             (lookupFM keyword pragma_keywords)
>   | otherwise = noPragma p (c:s)
>   where (keyword,rest) = span isIdent (c:s)

> lexBOL :: SuccessL a -> FailL a -> L a
> lexBOL success fail p s _ [] = lexToken success fail p s False []
> lexBOL success fail p s _ ctxt@(n:rest)
>   | col < n = success p (tok VRightBrace) p s True rest
>   | col == n = success p (tok VSemicolon) p s False ctxt
>   | otherwise = lexToken success fail p s False ctxt
>   where col = column p

> lexToken :: SuccessL a -> FailL a -> L a
> lexToken success fail p [] = success p (tok EOF) p []
> lexToken success fail p (c:s)
>   | c == '(' = token LeftParen
>   | c == ')' = token RightParen
>   | c == ',' = token Comma
>   | c == ';' = token Semicolon
>   | c == '[' = token LeftBracket
>   | c == ']' = token RightBracket
>   | c == '_' = token Underscore
>   | c == '`' = token Backquote
>   | c == '{' = token LeftBrace
>   | c == '}' = \bol -> token RightBrace bol . drop 1
>   | c == '\'' = lexChar p success fail (next p) s
>   | c == '\"' = lexString p success fail (next p) s
>   | isAlpha c = lexIdent (success p) p (c:s)
>   | isSym c = lexSym (success p) p (c:s)
>   | isDigit c = lexNumber (success p) p (c:s)
>   | otherwise = fail p ("Illegal character " ++ show c) p s
>   where token t = success p (tok t) (next p) s

> lexIdent :: (Token -> L a) -> L a
> lexIdent cont p s =
>   maybe (lexOptQual cont (token Id) [ident]) (cont . token)
>         (lookupFM ident reserved_and_special_ids)
>         (incr p (length ident)) rest
>   where (ident,rest) = span isIdent s
>         token t = idTok t [] ident

> lexSym :: (Token -> L a) -> L a
> lexSym cont p s
>   | "#-}" `isPrefixOf` s =            -- 3 == length "#-}"
>       cont (idTok PragmaEnd [] "#-}") (incr p 3) (drop 3 s)
>   | otherwise =
>       cont (token (maybe Sym id (lookupFM sym reserved_and_special_ops)))
>            (incr p (length sym)) rest
>   where (sym,rest) = span isSym s
>         token t = idTok t [] sym

> lexOptQual :: (Token -> L a) -> Token -> [String] -> L a
> lexOptQual cont token mIdent p ('.':c:s)
>   | isAlpha c = lexQualIdent cont identCont mIdent (next p) (c:s)
>   | isSym c = lexQualSym cont identCont mIdent (next p) (c:s)
>   where identCont _ _ = cont token p ('.':c:s)
> lexOptQual cont token mIdent p s = cont token p s

> lexQualIdent :: (Token -> L a) -> L a -> [String] -> L a
> lexQualIdent cont identCont mIdent p s =
>   maybe (lexOptQual cont (idTok QId mIdent ident) (mIdent ++ [ident]))
>         (const identCont)
>         (lookupFM ident reserved_ids)
>         (incr p (length ident)) rest
>   where (ident,rest) = span isIdent s

> lexQualSym :: (Token -> L a) -> L a -> [String] -> L a
> lexQualSym cont identCont mIdent p s =
>   maybe (cont (idTok QSym mIdent sym)) (const identCont)
>         (lookupFM sym reserved_ops)
>         (incr p (length sym)) rest
>   where (sym,rest) = span isSym s

> lexNumber :: (Token -> L a) -> L a
> lexNumber cont p ('0':c:s)
>   | c `elem` "oO" = lexOctal cont nullCont (incr p 2) s
>   | c `elem` "xX" = lexHexadecimal cont nullCont (incr p 2) s
>   where nullCont _ _ = cont (intTok 10 "0") (next p) (c:s)
> lexNumber cont p s =
>   lexOptFraction cont (intTok 10 digits) digits (incr p (length digits)) rest
>   where (digits,rest) = span isDigit s

> lexOctal :: (Token -> L a) -> L a -> L a
> lexOctal cont nullCont p s
>   | null digits = nullCont undefined undefined
>   | otherwise = cont (intTok 8 digits) (incr p (length digits)) rest
>   where (digits,rest) = span isOctit s

> lexHexadecimal :: (Token -> L a) -> L a -> L a
> lexHexadecimal cont nullCont p s
>   | null digits = nullCont undefined undefined
>   | otherwise = cont (intTok 16 digits) (incr p (length digits)) rest
>   where (digits,rest) = span isHexit s

> lexOptFraction :: (Token -> L a) -> Token -> String -> L a
> lexOptFraction cont _ mant p ('.':c:s)
>   | isDigit c = lexOptExponent cont (floatTok mant frac 0) mant frac
>                                (incr p (length frac+1)) rest
>   where (frac,rest) = span isDigit (c:s)
> lexOptFraction cont token mant p (c:s)
>   | c `elem` "eE" = lexSignedExponent cont intCont mant "" (next p) s
>   where intCont _ _ = cont token p (c:s)
> lexOptFraction cont token _ p s = cont token p s

> lexOptExponent :: (Token -> L a) -> Token -> String -> String -> L a
> lexOptExponent cont token mant frac p (c:s)
>   | c `elem` "eE" = lexSignedExponent cont floatCont mant frac (next p) s
>   where floatCont _ _ = cont token p (c:s)
> lexOptExponent cont token mant frac p s = cont token p s

> lexSignedExponent :: (Token -> L a) -> L a -> String -> String -> L a
> lexSignedExponent cont floatCont mant frac p ('+':c:s)
>   | isDigit c = lexExponent cont mant frac id (next p) (c:s)
> lexSignedExponent cont floatCont mant frac p ('-':c:s)
>   | isDigit c = lexExponent cont mant frac negate (next p) (c:s)
> lexSignedExponent cont floatCont mant frac p (c:s)
>   | isDigit c = lexExponent cont mant frac id p (c:s)
> lexSignedExponent cont floatCont mant frac p s = floatCont p s

> lexExponent :: (Token -> L a) -> String -> String -> (Int -> Int) -> L a
> lexExponent cont mant frac expSign p s =
>   cont (floatTok mant frac exp) (incr p (length digits)) rest
>   where (digits,rest) = span isDigit s
>         exp = expSign (convertIntegral 10 digits)

> lexChar :: Position -> SuccessL a -> FailL a -> L a
> lexChar p0 success fail p [] = fail p0 "Illegal character constant" p []
> lexChar p0 success fail p (c:s)
>   | c == '\\' = lexEscape p (lexCharEnd p0 success fail) fail (next p) s
>   | c == '\n' = fail p0 "Illegal character constant" p (c:s)
>   | c == '\t' = lexCharEnd p0 success fail c (tab p) s
>   | otherwise = lexCharEnd p0 success fail c (next p) s

> lexCharEnd :: Position -> SuccessL a -> FailL a -> Char -> L a
> lexCharEnd p0 success fail c p ('\'':s) = success p0 (charTok c) (next p) s
> lexCharEnd p0 success fail c p s =
>   fail p0 "Improperly terminated character constant" p s

> lexString :: Position -> SuccessL a -> FailL a -> L a
> lexString p0 success fail = lexStringRest p0 success fail ""

> lexStringRest :: Position -> SuccessL a -> FailL a -> String -> L a
> lexStringRest p0 success fail s0 p [] = 
>   fail p0 "Improperly terminated string constant" p []
> lexStringRest p0 success fail s0 p (c:s)
>   | c == '\\' =
>       lexStringEscape p (lexStringRest p0 success fail) fail s0 (next p) s
>   | c == '\"' = success p0 (stringTok (reverse s0)) (next p) s
>   | c == '\n' = fail p0 "Improperly terminated string constant" p []
>   | c == '\t' = lexStringRest p0 success fail (c:s0) (tab p) s
>   | otherwise = lexStringRest p0 success fail (c:s0) (next p) s

> lexStringEscape ::  Position -> (String -> L a) -> FailL a -> String -> L a
> lexStringEscape p0 success fail s0 p [] = lexEscape p0 undefined fail p []
> lexStringEscape p0 success fail s0 p (c:s)
>   | c == '&' = success s0 (next p) s
>   | isSpace c = lexStringGap (success s0) fail p (c:s)
>   | otherwise = lexEscape p0 (success . (:s0)) fail p (c:s)

> lexStringGap :: L a -> FailL a -> L a
> lexStringGap success fail p [] = fail p "End of file in string gap" p []
> lexStringGap success fail p (c:s)
>   | c == '\\' = success (next p) s
>   | c == '\t' = lexStringGap success fail (tab p) s
>   | c == '\n' = lexStringGap success fail (nl p) s
>   | isSpace c = lexStringGap success fail (next p) s
>   | otherwise = fail p ("Illegal character in string gap " ++ show c) p s

> lexEscape :: Position -> (Char -> L a) -> FailL a -> L a
> lexEscape p0 success fail p ('a':s) = success '\a' (next p) s
> lexEscape p0 success fail p ('b':s) = success '\b' (next p) s
> lexEscape p0 success fail p ('f':s) = success '\f' (next p) s
> lexEscape p0 success fail p ('n':s) = success '\n' (next p) s
> lexEscape p0 success fail p ('r':s) = success '\r' (next p) s
> lexEscape p0 success fail p ('t':s) = success '\t' (next p) s
> lexEscape p0 success fail p ('v':s) = success '\v' (next p) s
> lexEscape p0 success fail p ('\\':s) = success '\\' (next p) s
> lexEscape p0 success fail p ('"':s) = success '\"' (next p) s
> lexEscape p0 success fail p ('\'':s) = success '\'' (next p) s
> lexEscape p0 success fail p ('^':c:s)
>   | isUpper c || c `elem` "@[\\]^_" =
>       success (chr (ord c `mod` 32)) (incr p 2) s
> lexEscape p0 success fail p ('o':c:s)
>   | isOctit c = numEscape p0 success fail 8 isOctit (next p) (c:s)
> lexEscape p0 success fail p ('x':c:s)
>   | isHexit c = numEscape p0 success fail 16 isHexit (next p) (c:s)
> lexEscape p0 success fail p (c:s)
>   | isDigit c = numEscape p0 success fail 10 isDigit p (c:s)
> lexEscape p0 success fail p s = asciiEscape p0 success fail p s

> asciiEscape :: Position -> (Char -> L a) -> FailL a -> L a
> asciiEscape p0 success fail p ('N':'U':'L':s) = success '\NUL' (incr p 3) s
> asciiEscape p0 success fail p ('S':'O':'H':s) = success '\SOH' (incr p 3) s
> asciiEscape p0 success fail p ('S':'T':'X':s) = success '\STX' (incr p 3) s
> asciiEscape p0 success fail p ('E':'T':'X':s) = success '\ETX' (incr p 3) s
> asciiEscape p0 success fail p ('E':'O':'T':s) = success '\EOT' (incr p 3) s
> asciiEscape p0 success fail p ('E':'N':'Q':s) = success '\ENQ' (incr p 3) s
> asciiEscape p0 success fail p ('A':'C':'K':s) = success '\ACK' (incr p 3) s 
> asciiEscape p0 success fail p ('B':'E':'L':s) = success '\BEL' (incr p 3) s
> asciiEscape p0 success fail p ('B':'S':s) = success '\BS' (incr p 2) s
> asciiEscape p0 success fail p ('H':'T':s) = success '\HT' (incr p 2) s
> asciiEscape p0 success fail p ('L':'F':s) = success '\LF' (incr p 2) s
> asciiEscape p0 success fail p ('V':'T':s) = success '\VT' (incr p 2) s
> asciiEscape p0 success fail p ('F':'F':s) = success '\FF' (incr p 2) s
> asciiEscape p0 success fail p ('C':'R':s) = success '\CR' (incr p 2) s
> asciiEscape p0 success fail p ('S':'O':s) = success '\SO' (incr p 2) s
> asciiEscape p0 success fail p ('S':'I':s) = success '\SI' (incr p 2) s
> asciiEscape p0 success fail p ('D':'L':'E':s) = success '\DLE' (incr p 3) s 
> asciiEscape p0 success fail p ('D':'C':'1':s) = success '\DC1' (incr p 3) s
> asciiEscape p0 success fail p ('D':'C':'2':s) = success '\DC2' (incr p 3) s
> asciiEscape p0 success fail p ('D':'C':'3':s) = success '\DC3' (incr p 3) s
> asciiEscape p0 success fail p ('D':'C':'4':s) = success '\DC4' (incr p 3) s
> asciiEscape p0 success fail p ('N':'A':'K':s) = success '\NAK' (incr p 3) s
> asciiEscape p0 success fail p ('S':'Y':'N':s) = success '\SYN' (incr p 3) s
> asciiEscape p0 success fail p ('E':'T':'B':s) = success '\ETB' (incr p 3) s
> asciiEscape p0 success fail p ('C':'A':'N':s) = success '\CAN' (incr p 3) s 
> asciiEscape p0 success fail p ('E':'M':s) = success '\EM' (incr p 2) s
> asciiEscape p0 success fail p ('S':'U':'B':s) = success '\SUB' (incr p 3) s
> asciiEscape p0 success fail p ('E':'S':'C':s) = success '\ESC' (incr p 3) s
> asciiEscape p0 success fail p ('F':'S':s) = success '\FS' (incr p 2) s
> asciiEscape p0 success fail p ('G':'S':s) = success '\GS' (incr p 2) s
> asciiEscape p0 success fail p ('R':'S':s) = success '\RS' (incr p 2) s
> asciiEscape p0 success fail p ('U':'S':s) = success '\US' (incr p 2) s
> asciiEscape p0 success fail p ('S':'P':s) = success '\SP' (incr p 2) s
> asciiEscape p0 success fail p ('D':'E':'L':s) = success '\DEL' (incr p 3) s
> asciiEscape p0 success fail p s = fail p0 "Illegal escape sequence" p s

\end{verbatim}
The \texttt{numEscape} lexer accepts character codes in the character
range supported by the Haskell compiler. Note that hbc and nhc98 up to
(at least) version 1.18 report \texttt{(maxBound::Char) == 255}, even
though they actually support a larger character set range.
\begin{verbatim}

> numEscape :: Position -> (Char -> L a) -> FailL a -> Int
>           -> (Char -> Bool) -> L a
> numEscape p0 success fail b isDigit p s
>   | n >= min && n <= max = success (chr n) (incr p (length digits)) rest
>   | otherwise = fail p0 "Numeric escape out-of-range" p s
>   where (digits,rest) = span isDigit s
>         n = convertIntegral b digits
>         min = ord minBound
>         max = ord maxBound

\end{verbatim}
