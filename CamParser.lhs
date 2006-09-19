% -*- LaTeX -*-
% $Id: CamParser.lhs 1866 2006-03-02 17:34:02Z wlux $
%
% Copyright (c) 1999-2005, Wolfgang Lux
% See LICENSE for the full license.
%
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
>   | IntAttributes{ ival :: Int }
>   | FloatAttributes{ fval :: Double }

> tok :: Category -> Token
> tok c = Token c NoAttributes

> nameTok :: Category -> String -> Token
> nameTok c cs = Token c NameAttributes{ sval = cs }

> intTok :: Category -> String -> Token
> intTok c cs = Token c IntAttributes{ ival = convertSignedIntegral 10 cs }

> floatTok :: String -> String -> String -> Token
> floatTok mant frac exp =
>   Token FloatNum FloatAttributes{ fval = convertSignedFloating mant frac e }
>   where e = convertSignedIntegral 10 exp

> data Keyword =
>     KW_bool
>   | KW_ccall
>   | KW_char
>   | KW_choices
>   | KW_data
>   | KW_default
>   | KW_enter
>   | KW_exec
>   | KW_flex
>   | KW_float
>   | KW_free
>   | KW_function
>   | KW_import
>   | KW_int
>   | KW_lazy
>   | KW_let
>   | KW_lock
>   | KW_papp
>   | KW_pointer
>   | KW_return
>   | KW_rigid
>   | KW_stable
>   | KW_switch
>   | KW_unit
>   | KW_update
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
>   showsPrec _ KW_choices = showKeyword "choices"
>   showsPrec _ KW_data = showKeyword "data"
>   showsPrec _ KW_default = showKeyword "default"
>   showsPrec _ KW_enter = showKeyword "enter"
>   showsPrec _ KW_exec = showKeyword "exec"
>   showsPrec _ KW_flex = showKeyword "flex"
>   showsPrec _ KW_float = showKeyword "float"
>   showsPrec _ KW_free = showKeyword "free"
>   showsPrec _ KW_function = showKeyword "function"
>   showsPrec _ KW_import = showKeyword "import"
>   showsPrec _ KW_int = showKeyword "int"
>   showsPrec _ KW_lazy = showKeyword "lazy"
>   showsPrec _ KW_let = showKeyword "let"
>   showsPrec _ KW_lock = showKeyword "lock"
>   showsPrec _ KW_papp = showKeyword "papp"
>   showsPrec _ KW_pointer = showKeyword "pointer"
>   showsPrec _ KW_return = showKeyword "return"
>   showsPrec _ KW_rigid = showKeyword "rigid"
>   showsPrec _ KW_stable = showKeyword "stable"
>   showsPrec _ KW_switch = showKeyword "switch"
>   showsPrec _ KW_unit = showKeyword "unit"
>   showsPrec _ KW_update = showKeyword "update"

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
>     ("choices",  KW_choices),
>     ("data",     KW_data),
>     ("default",  KW_default),
>     ("enter",    KW_enter),
>     ("exec",     KW_exec),
>     ("flex",     KW_flex),
>     ("float",    KW_float),
>     ("free",     KW_free),
>     ("function", KW_function),
>     ("import",   KW_import),
>     ("int",      KW_int),
>     ("lazy",     KW_lazy),
>     ("let",      KW_let),
>     ("lock",     KW_lock),
>     ("papp",     KW_papp),
>     ("pointer",  KW_pointer),
>     ("return",   KW_return),
>     ("rigid",    KW_rigid),
>     ("stable",   KW_stable),
>     ("switch",   KW_switch),
>     ("unit",     KW_unit),
>     ("update",   KW_update)
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
>   | c == '-' =
>       case cs of
>         ('-':cs') -> lexer success fail p (dropWhile (/= '\n') cs')
>         ('>':cs') -> token2 RightArrow cs'
>         _ -> illegalChar
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
>   | c == '"' = lexString (success p . nameTok String . id) fail (next p) cs
>   | c == '.' = lexKeyword (success p) fail p cs
>   | isAlpha c || c == '_' = lexIdent (success p) c p cs
>   | isDigit c || c `elem` "+-" = lexNumber (success p) fail c p cs
>   | otherwise = illegalChar
>   where token t = success p (tok t) (next p) cs
>         token2 t = success p (tok t) (incr p 2)
>         advance '\n' = nl
>         advance '\t' = tab
>         advance _ = next
>         illegalChar = fail p ("Illegal character " ++ show c) p (c:cs)

> lexIdent :: (Token -> L a) -> Char -> L a
> lexIdent success c p cs =
>   success (nameTok Ident (c : cs')) (incr p (1 + length cs')) cs''
>   where (cs',cs'') = span isIdent cs

> lexKeyword :: (Token -> L a) -> FailL a -> L a
> lexKeyword success fail p cs
>   | null cs' = fail p "Keyword expected after '.'" (next p) cs
>   | otherwise =
>       maybe (fail p ("Unknown keyword " ++ show ('.':cs')))
>             (success . tok . Keyword)
>             (lookupFM cs' keywords) (incr p (1 + length cs')) cs''
>   where (cs',cs'') = span isIdent cs

> lexNumber :: (Token -> L a) -> FailL a -> Char -> L a
> lexNumber success fail c p cs
>   | null ds && not (isDigit c) =
>      fail p ("Digit expected after " ++ show c) (next p) cs
>   | otherwise =
>       case cs' of
>         ('.':cs'') -> lexFraction success fail (c:ds) (next p') cs''
>         ('e':cs'') -> lexExponent success fail (c:ds) "" (next p') cs''
>         ('E':cs'') -> lexExponent success fail (c:ds) "" (next p') cs''
>         _ -> success (intTok IntNum (c:ds)) p' cs'
>   where (ds,cs' ) = span isDigit cs
>         p' = incr p (1 + length ds)

> lexFraction :: (Token -> L a) -> FailL a -> String -> L a
> lexFraction success fail ds p cs =
>   case cs' of
>     ('e':cs'') -> lexExponent success fail ds ds' (next p') cs''
>     ('E':cs'') -> lexExponent success fail ds ds' (next p') cs''
>     _ -> success (floatTok ds ds' "") p' cs'
>   where (ds',cs') = span isDigit cs
>         p' = incr p (length ds')

> lexExponent :: (Token -> L a) -> FailL a -> String -> String -> L a
> lexExponent success fail ds ds' p (c:cs)
>   | isDigit c || c `elem` "+-" =
>       case span isDigit cs of
>         (es,cs')
>           | not (isDigit c) && null es -> fail p "Empty exponent" p cs
>           | otherwise ->
>               success (floatTok ds ds' (c:es)) (incr p (1 + length es)) cs'
> lexExponent success fail _ _ p cs = fail p "Exponent expected" p cs

> lexString :: (String -> L a) -> FailL a -> L a
> lexString success fail p [] = fail p "Unterminated string constant" p []
> lexString success fail p (c:cs)
>   | c == '"' = success "" (next p) cs
>   | c == '\n' = fail p "Unterminated string constant" p []
>   | c == '\t' = lexString (success . (c:)) fail (tab p) cs
>   | c < ' ' = fail p "Illegal character in string constant" p cs
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
> funcDecl =
>   FunctionDecl <$-> keyword KW_function <*> checkName <*> nameList <*> block

> block :: Parser Token Stmt a
> block = braces stmt

> stmt :: Parser Token Stmt a
> stmt = Return <$-> keyword KW_return <*> node
>    <|> Enter <$-> keyword KW_enter <*> checkName
>    <|> Exec <$-> keyword KW_exec <*> checkName <*> nameList
>    <|> CCall <$-> keyword KW_ccall <*> (Just <$> string `opt` Nothing)
>              <*> parens cRetType <*> cCall
>    <|> Seq <$> stmt0 <*-> checkSemi <*> stmt
>    <|> flip Switch <$-> keyword KW_switch <*> checkName <*> rf
>                    <*> braces cases
>    <|> Choices <$-> keyword KW_choices <*> braces (block `sepBy1` bar)
>    <|> block
>    where rf = Rigid <$-> keyword KW_rigid <|> Flex <$-> keyword KW_flex

> stmt0 :: Parser Token Stmt0 a
> stmt0 = Lock <$-> keyword KW_lock <*> checkName
>     <|> Update <$-> keyword KW_update <*> checkName <*> checkName
>     <|> (:<-) <$> name <*-> checkLeftArrow <*> stmt <\> stmt0
>     <|> Let <$-> keyword KW_let <*> braces (binding `sepBy1` semi)

> binding :: Parser Token Bind a
> binding = Bind <$> name <*-> checkEquals <*> node

> node :: Parser Token Expr a
> node = Lit <$> literal
>    <|> Constr <$-> keyword KW_data <*> checkName <*> nameList
>    <|> Papp <$-> keyword KW_papp <*> checkName <*> nameList
>    <|> Closure <$-> keyword KW_function <*> checkName <*> nameList
>    <|> Lazy <$-> keyword KW_lazy <*> checkName <*> nameList
>    <|> Free <$-> keyword KW_free
>    <|> Var <$> name

> cases :: Parser Token [Case] a
> cases = return <$> switchCase defaultTag
>     <|> (:) <$> switchCase caseTag <*> (bar <-*> cases `opt` [])
>   where switchCase tag = Case <$> tag <*-> checkColon <*> block

> literal :: Parser Token Literal a
> literal = Char . toEnum <$-> keyword KW_char <*> checkInt
>       <|> Int <$-> keyword KW_int <*> checkInt
>       <|> Float <$-> keyword KW_float <*> checkFloat

> cCall :: Parser Token CCall a
> cCall = StaticCall <$> (show <$> name) <*> parenList arg
>     <|> DynamicCall <$> parens (checkAsterisk <-*> checkName)
>                     <*> parenList arg
>     <|> StaticAddr <$-> ampersand <*> (show <$> checkName)
>   where arg = (,) <$> parens cArgType <*> checkName

> cRetType :: Parser Token CRetType a
> cRetType = Nothing <$-> keyword KW_unit <|> Just <$> cArgType

> cArgType :: Parser Token CArgType a
> cArgType = TypeBool <$-> keyword KW_bool
>        <|> TypeChar <$-> keyword KW_char
>        <|> TypeInt <$-> keyword KW_int
>        <|> TypeFloat <$-> keyword KW_float
>        <|> TypePtr <$-> keyword KW_pointer
>        <|> TypeFunPtr <$-> keyword KW_function
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

> int,checkInt :: Parser Token Int a
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

> leftArrow, checkLeftArrow :: Parser Token Attributes a
> leftArrow = token LeftArrow
> checkLeftArrow = leftArrow <?> "<- expected"

> rightArrow :: Parser Token Attributes a
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
