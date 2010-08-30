% -*- LaTeX -*-
% $Id: CamParser.lhs 3001 2010-08-30 19:39:16Z wlux $
%
% Copyright (c) 1999-2009, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CamParser.lhs}
\subsection{Parsing Abstract Machine Code}
In this section, a lexer and parser for the abstract machine code are
presented, which are based on the LL(1) parsing combinators described
in appendix~\ref{sec:ll-parsecomb}.
\begin{verbatim}

> module CamParser(parseModule) where
> import Cam
> import Position
> import LexComb
> import LLParseComb
> import Map
> import Char
> import Maybe
> import Error

\end{verbatim}
\paragraph{Lexer}
\begin{verbatim}

> data Token = Token Category Attributes

> instance Eq Token where
>   Token t1 _ == Token t2 _ = t1 == t2
> instance Ord Token where
>   Token t1 _ `compare` Token t2 _ = t1 `compare` t2

> data Category =
>   -- identifiers
>     Ident | Keyword Keyword
>   -- numbers
>   | IntNum | FloatNum
>   -- strings
>   | String
>   -- symbols
>   | Equals | Colon | Comma | Semicolon
>   | Bar | Ampersand | Asterisk | LeftArrow | RightArrow
>   | LeftParen | RightParen | LeftBrace | RightBrace
>   -- end-of-file
>   | EOF
>   deriving (Eq,Ord)

> data Attributes =
>     NoAttributes
>   | NameAttributes{ sval :: String }
>   | IntAttributes{ ival :: Integer }
>   | FloatAttributes{ fval :: Double }

> tok :: Category -> Token
> tok c = Token c NoAttributes

> nameTok :: Category -> String -> Token
> nameTok c cs = Token c NameAttributes{ sval = cs }

> intTok :: String -> Token
> intTok cs = Token IntNum IntAttributes{ ival = convertSignedIntegral 10 cs }

> floatTok :: String -> String -> Int -> Token
> floatTok mant frac exp =
>   Token FloatNum FloatAttributes{ fval = convertSignedFloat mant frac exp }

> data Keyword =
>     KW_bool
>   | KW_ccall
>   | KW_char
>   | KW_choice
>   | KW_data
>   | KW_default
>   | KW_eval
>   | KW_flex
>   | KW_float
>   | KW_free
>   | KW_fun
>   | KW_import
>   | KW_in
>   | KW_int
>   | KW_integer
>   | KW_lazy
>   | KW_let
>   | KW_papp
>   | KW_pointer
>   | KW_return
>   | KW_rigid
>   | KW_stable
>   | KW_switch
>   | KW_unit
>   deriving (Eq,Ord)

> instance Show Attributes where
>   showsPrec _ NoAttributes = showChar '_'
>   showsPrec _ (NameAttributes sval) =
>     showChar '`' . showString sval . showChar '\''
>   showsPrec _ (IntAttributes ival) = shows ival
>   showsPrec _ (FloatAttributes fval) = shows fval

> instance Show Token where
>   showsPrec _ (Token Ident a) = shows a
>   showsPrec _ (Token (Keyword k) _) = showChar '`' . shows k . showChar '\''
>   showsPrec _ (Token IntNum a) = showString "integer " . shows a
>   showsPrec _ (Token FloatNum a) = showString "float " . shows a
>   showsPrec _ (Token String a) = showString "string " . shows a
>   showsPrec _ (Token Equals _) = showString "="
>   showsPrec _ (Token Colon _) = showString "`:'"
>   showsPrec _ (Token Comma _) = showString "`,'"
>   showsPrec _ (Token Semicolon _) = showString "`;'"
>   showsPrec _ (Token Bar _) = showString "`|'"
>   showsPrec _ (Token Ampersand _) = showString "`&'"
>   showsPrec _ (Token Asterisk _) = showString "`*'"
>   showsPrec _ (Token LeftArrow _) = showString "`<-'"
>   showsPrec _ (Token RightArrow _) = showString "`->'"
>   showsPrec _ (Token LeftParen _) = showString "`('"
>   showsPrec _ (Token RightParen _) = showString "`)'"
>   showsPrec _ (Token LeftBrace _) = showString "`{'"
>   showsPrec _ (Token RightBrace _) = showString "`}'"
>   showsPrec _ (Token EOF _) = showString "end-of-file"

> instance Show Keyword where
>   showsPrec _ KW_bool = showKeyword "bool"
>   showsPrec _ KW_ccall = showKeyword "ccall"
>   showsPrec _ KW_char = showKeyword "char"
>   showsPrec _ KW_choice = showKeyword "choice"
>   showsPrec _ KW_data = showKeyword "data"
>   showsPrec _ KW_default = showKeyword "default"
>   showsPrec _ KW_eval = showKeyword "eval"
>   showsPrec _ KW_flex = showKeyword "flex"
>   showsPrec _ KW_float = showKeyword "float"
>   showsPrec _ KW_free = showKeyword "free"
>   showsPrec _ KW_fun = showKeyword "fun"
>   showsPrec _ KW_import = showKeyword "import"
>   showsPrec _ KW_in = showKeyword "in"
>   showsPrec _ KW_int = showKeyword "int"
>   showsPrec _ KW_integer = showKeyword "integer"
>   showsPrec _ KW_lazy = showKeyword "lazy"
>   showsPrec _ KW_let = showKeyword "let"
>   showsPrec _ KW_papp = showKeyword "papp"
>   showsPrec _ KW_pointer = showKeyword "pointer"
>   showsPrec _ KW_return = showKeyword "return"
>   showsPrec _ KW_rigid = showKeyword "rigid"
>   showsPrec _ KW_stable = showKeyword "stable"
>   showsPrec _ KW_switch = showKeyword "switch"
>   showsPrec _ KW_unit = showKeyword "unit"

> showKeyword :: String -> ShowS
> showKeyword kw = showChar '.' . showString kw

> instance Symbol Token where
>   isEOF (Token t _) = t == EOF

> isIdent :: Char -> Bool
> isIdent c = isAlphaNum c || c == '_'

> keywords :: FM String Keyword
> keywords = fromListFM [
>     ("bool",     KW_bool),
>     ("ccall",    KW_ccall),
>     ("char",     KW_char),
>     ("choice",   KW_choice),
>     ("data",     KW_data),
>     ("default",  KW_default),
>     ("eval",     KW_eval),
>     ("flex",     KW_flex),
>     ("float",    KW_float),
>     ("free",     KW_free),
>     ("fun",      KW_fun),
>     ("import",   KW_import),
>     ("in",       KW_in),
>     ("int",      KW_int),
>     ("integer",  KW_integer),
>     ("lazy",     KW_lazy),
>     ("let",      KW_let),
>     ("papp",     KW_papp),
>     ("pointer",  KW_pointer),
>     ("return",   KW_return),
>     ("rigid",    KW_rigid),
>     ("stable",   KW_stable),
>     ("switch",   KW_switch),
>     ("unit",     KW_unit)
>   ]

> type SuccessL a = Position -> Token -> L a
> type FailL a = Position -> String -> L a

> lexFile :: L [(Position,Token)]
> lexFile = lexer tokens failL
>   where tokens p t
>           | isEOF t = returnL [(p,t)]
>           | otherwise = lexFile `thenL` returnL . ((p,t):)

> lexer :: SuccessL a -> FailL a -> L a
> lexer success fail p [] = success p (tok EOF) p []
> lexer success fail p (c:cs)
>   | isSpace c = lexer success fail (advance c p) cs
>   | c == '+' = lexNumber (success p) fail (c:) (next p) cs
>   | c == '-' =
>       case cs of
>         ('-':cs') -> lexer success fail p (dropWhile (/= '\n') cs')
>         ('>':cs') -> token2 RightArrow cs'
>         _ -> lexNumber (success p) fail (c:) (next p) cs
>   | c == '=' = token Equals
>   | c == ':' = token Colon
>   | c == ',' = token Comma
>   | c == ';' = token Semicolon
>   | c == '|' = token Bar
>   | c == '&' = token Ampersand
>   | c == '*' = token Asterisk
>   | c == '<' =
>       case cs of
>         ('-':cs') -> token2 LeftArrow cs'
>         _ -> illegalChar
>   | c == '(' = token LeftParen
>   | c == ')' = token RightParen
>   | c == '{' = token LeftBrace
>   | c == '}' = token RightBrace
>   | c == '"' = lexString (success p . nameTok String) fail (next p) cs
>   | c == '.' = lexKeyword (success p . tok . Keyword) fail (next p) cs
>   | isAlpha c || c == '_' = lexIdent (success p . nameTok Ident) p (c:cs)
>   | isDigit c = lexNumber (success p) fail id p (c:cs)
>   | otherwise = illegalChar
>   where token t = success p (tok t) (next p) cs
>         token2 t = success p (tok t) (incr p 2)
>         advance '\n' = nl
>         advance '\t' = tab
>         advance _ = next
>         illegalChar = fail p ("Illegal character " ++ show c) p (c:cs)

> lexIdent :: (String -> L a) -> L a
> lexIdent success p cs = success ident (incr p (length ident)) rest
>   where (ident,rest) = span isIdent cs

> lexKeyword :: (Keyword -> L a) -> FailL a -> L a
> lexKeyword success fail p cs
>   | null keyword = fail p "Keyword expected after '.'" p cs
>   | otherwise =
>       maybe (fail p ("Unknown keyword " ++ show ('.':keyword)))
>             success
>             (lookupFM keyword keywords) (incr p (length keyword)) rest
>   where (keyword,rest) = span isIdent cs

> lexNumber :: (Token -> L a) -> FailL a -> (String -> String) -> L a
> lexNumber success fail f p cs
>   | null digits = fail p ("Digit expected after " ++ show (head (f ""))) p cs
>   | otherwise = lexOptFraction float int p' rest
>   where p' = incr p (length digits)
>         (digits,rest) = span isDigit cs
>         int _ _ = success (intTok (f digits)) p' rest
>         float frac exp = success (floatTok (f digits) frac exp)

> lexOptFraction :: (String -> Int -> L a) -> L a -> L a
> lexOptFraction success _ p ('.':cs) = lexFraction success (next p) cs
> lexOptFraction success noFrac p cs = lexOptExponent (success "") noFrac p cs

> lexFraction :: (String -> Int -> L a) -> L a
> lexFraction success p cs = lexOptExponent (success frac) noExp p' rest
>   where p' = incr p (length frac)
>         (frac,rest) = span isDigit cs
>         noExp _ _ = success frac 0 p' rest

> lexOptExponent :: (Int -> L a) -> L a -> L a
> lexOptExponent success noExp p (c:cs)
>   | c `elem` "eE" = lexSignedExponent success noExp (next p) cs
> lexOptExponent _ noExp p cs = noExp p cs

> lexSignedExponent :: (Int -> L a) -> L a -> L a
> lexSignedExponent success noExp p ('+':cs) =
>   lexExponent success noExp (next p) cs
> lexSignedExponent success noExp p ('-':cs) =
>   lexExponent (success . negate) noExp (next p) cs
> lexSignedExponent success noExp p cs = lexExponent success noExp p cs

> lexExponent :: (Int -> L a) -> L a -> L a
> lexExponent success noExp p cs
>   | null digits = noExp p cs
>   | otherwise = success (exp) (incr p (length digits)) rest
>   where (digits,rest) = span isDigit cs
>         exp = convertIntegral 10 digits

> lexString :: (String -> L a) -> FailL a -> L a
> lexString _ fail p [] = fail p "Unterminated string constant" p []
> lexString success fail p (c:cs)
>   | c == '\"' = success "" (next p) cs
>   | c == '\n' = fail p "Unterminated string constant" p (c:cs)
>   | c == '\t' = lexString (success . (c:)) fail (tab p) cs
>   | c < ' ' = fail p "Illegal character in string constant" p (c:cs)
>   | otherwise = lexString (success . (c:)) fail (next p) cs

\end{verbatim}
\paragraph{Parser}
\begin{verbatim}

> parseModule :: FilePath -> String -> Error Module
> parseModule fn s = applyParser camModule lexer fn s

> camModule :: Parser Token Module a
> camModule = (:) <$> importDecl <*> (semi <-*> camModule `opt` [])
>         <|> camDecl `sepBy` semi

> camDecl :: Parser Token Decl a
> camDecl = dataDecl <|> funcDecl

> importDecl :: Parser Token Decl a
> importDecl = ImportDecl <$-> keyword KW_import <*> checkName

> dataDecl :: Parser Token Decl a
> dataDecl = DataDecl <$-> keyword KW_data <*> checkName <*> (nameList `opt` [])
>                     <*> (equals <-*> (constrDecl `sepBy1` bar) `opt` [])

> constrDecl :: Parser Token ConstrDecl a
> constrDecl = ConstrDecl <$> name <*> (parenList typ `opt` [])

> typ, atyp :: Parser Token Type a
> typ = atyp `chainr1` (TypeArr <$-> rightArrow)
> atyp = name <**> (flip TypeApp <$> parenList typ `opt` TypeVar)

> funcDecl :: Parser Token Decl a
> funcDecl = FunctionDecl <$> name <*> nameList <*> braces stmt

> stmt :: Parser Token Stmt a
> stmt = name <**> nameStmt
>    <|> Let <$-> keyword KW_let <*> braces (binding `sepBy1` semi)
>            <*-> keyword KW_in <*> stmt
>    <|> astmt <\> name
>  where nameStmt = flip Exec <$> nameList
>               <|> stmtSeq <$-> leftArrow <*> astmt <*-> checkSemi <*> stmt
>        stmtSeq st1 st2 v = Seq (v :<- st1) st2

> astmt :: Parser Token Stmt a
> astmt = Return <$-> keyword KW_return <*> node
>     <|> Eval <$-> keyword KW_eval <*> checkName
>     <|> Exec <$> name <*> nameList
>     <|> CCall <$-> keyword KW_ccall <*> (Just <$> string `opt` Nothing)
>               <*> (parens cRetType `opt` Just TypeNodePtr) <*> cCall
>     <|> flip Switch <$-> keyword KW_switch <*> checkName <*> rf
>                     <*> braces cases
>     <|> Choice <$-> keyword KW_choice <*> braces (stmt `sepBy` bar)
>     <|> leftBrace <-*> stmt <*-> rightBrace
>   where rf = Rigid <$-> keyword KW_rigid <|> Flex <$-> keyword KW_flex

> binding :: Parser Token Bind a
> binding = Bind <$> name <*-> checkEquals <*> node

> node :: Parser Token Expr a
> node = Lit <$> literal
>    <|> Constr <$-> keyword KW_data <*> checkName <*> nameList
>    <|> Papp <$-> keyword KW_papp <*> checkName <*> nameList
>    <|> Closure <$-> keyword KW_fun <*> checkName <*> nameList
>    <|> Lazy <$-> keyword KW_lazy <*> checkName <*> nameList
>    <|> Free <$-> keyword KW_free
>    <|> Var <$> name

> cases :: Parser Token [Case] a
> cases = return <$> switchCase defaultTag
>     <|> (:) <$> switchCase caseTag <*> (bar <-*> cases `opt` [])
>   where switchCase tag = Case <$> tag <*-> checkColon <*> stmt

> literal :: Parser Token Literal a
> literal = Char . toEnum . fromInteger <$-> keyword KW_char <*> checkInt
>       <|> Int <$-> keyword KW_int <*> checkInt
>       <|> Integer <$-> keyword KW_integer <*> checkInt
>       <|> Float <$-> keyword KW_float <*> checkFloat

> cCall :: Parser Token CCall a
> cCall = StaticCall <$> (show <$> name) <*> parenList arg
>     <|> DynamicCall <$> parens (checkAsterisk <-*> checkName)
>                     <*> parenList arg
>     <|> StaticAddr <$-> ampersand <*> (show <$> checkName)
>   where arg = (,) <$> parens cArgType <*> checkName
>           <|> (,) TypeNodePtr <$> name

> cRetType :: Parser Token CRetType a
> cRetType = Nothing <$-> keyword KW_unit <|> Just <$> cArgType

> cArgType :: Parser Token CArgType a
> cArgType = TypeBool <$-> keyword KW_bool
>        <|> TypeChar <$-> keyword KW_char
>        <|> TypeInt <$-> keyword KW_int
>        <|> TypeFloat <$-> keyword KW_float
>        <|> TypePtr <$-> keyword KW_pointer
>        <|> TypeFunPtr <$-> keyword KW_fun
>        <|> TypeStablePtr <$-> keyword KW_stable

> name, checkName :: Parser Token Name a
> name = Name . sval <$> token Ident
> checkName = name <?> "name expected"

> nameList :: Parser Token [Name] a
> nameList = parenList name

> parenList :: Parser Token a b -> Parser Token [a] b
> parenList p = parens (p `sepBy` comma)

> keyword :: Keyword -> Parser Token Attributes a
> keyword k = token (Keyword k)

> int,checkInt :: Parser Token Integer a
> int = ival <$> token IntNum
> checkInt = int <?> "integer number expected"

> float,checkFloat :: Parser Token Double a
> float = fval <$> token FloatNum
> checkFloat = float <?> "floating point number expected"

> string :: Parser Token String a
> string = sval <$> token String

> caseTag :: Parser Token Tag a
> caseTag = LitCase <$> literal
>       <|> ConstrCase <$-> keyword KW_data <*> checkName <*> nameList

> defaultTag :: Parser Token Tag a
> defaultTag = DefaultCase <$-> keyword KW_default

> token :: Category -> Parser Token Attributes a
> token c = attr <$> symbol (Token c NoAttributes)
>   where attr (Token _ a) = a

> equals, checkEquals :: Parser Token Attributes a
> equals = token Equals
> checkEquals = equals <?> "= expected"

> comma :: Parser Token Attributes a
> comma = token Comma

> colon, checkColon :: Parser Token Attributes a
> colon = token Colon
> checkColon = colon <?> ": expected"

> semi, checkSemi :: Parser Token Attributes a
> semi = token Semicolon
> checkSemi = semi <?> "; expected"

> bar :: Parser Token Attributes a
> bar = token Bar

> ampersand :: Parser Token Attributes a
> ampersand = token Ampersand

> asterisk, checkAsterisk :: Parser Token Attributes a
> asterisk = token Asterisk
> checkAsterisk = asterisk <?> "* expected"

> leftArrow, rightArrow :: Parser Token Attributes a
> leftArrow = token LeftArrow
> rightArrow = token RightArrow

> leftParen, rightParen :: Parser Token Attributes a
> leftParen = token LeftParen
> rightParen = token RightParen

> leftBrace, rightBrace :: Parser Token Attributes a
> leftBrace = token LeftBrace
> rightBrace = token RightBrace

> parens, braces :: Parser Token a b -> Parser Token a b
> parens p = leftParen <-*> p <*-> rightParen
> braces p = leftBrace <-*> p <*-> rightBrace
>        <?> "{ expected"

\end{verbatim}
