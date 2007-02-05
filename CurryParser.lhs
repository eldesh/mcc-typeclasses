% -*- LaTeX -*-
% $Id: CurryParser.lhs 2088 2007-02-05 09:27:49Z wlux $
%
% Copyright (c) 1999-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CurryParser.lhs}
\section{A Parser for Curry}
The Curry parser is implemented using the (mostly) LL(1) parsing
combinators described in appendix~\ref{sec:ll-parsecomb}.
\begin{verbatim}

> module CurryParser where
> import Ident
> import Position
> import Error
> import LexComb
> import LLParseComb
> import CurrySyntax
> import CurryLexer
> import PathUtils

> instance Symbol Token where
>   isEOF (Token c _) = c == EOF

\end{verbatim}
\paragraph{Modules}
\begin{verbatim}

> parseSource :: FilePath -> String -> Error (Module ())
> parseSource fn = applyParser (parseModule fn) lexer fn

> parseHeader :: FilePath -> String -> Error (Module ())
> parseHeader fn = prefixParser (moduleHeader fn <*->
>                               (leftBrace `opt` undefined) <*>
>                                many (importDecl <*-> many semicolon) <*>
>                                succeed [])
>                               lexer
>                               fn

> parseModule :: FilePath -> Parser Token (Module ()) a
> parseModule fn = uncurry <$> moduleHeader fn <*> layout moduleDecls

> moduleHeader :: FilePath
>              -> Parser Token ([ImportDecl] -> [TopDecl ()] -> Module ()) a
> moduleHeader fn = Module <$-> token KW_module
>                          <*> (mIdent <?> "module name expected")
>                          <*> (Just <$> exportSpec `opt` Nothing)
>                          <*-> (token KW_where <?> "where expected")
>             `opt` Module (defaultMIdent fn) Nothing

> exportSpec :: Parser Token ExportSpec a
> exportSpec = Exporting <$> position <*> parens (export `sepBy` comma)

> export :: Parser Token Export a
> export = qtycon <**> (parens spec `opt` Export)
>      <|> Export <$> qfun <\> qtycon
>      <|> ExportModule <$-> token KW_module <*> mIdent
>   where spec = ExportTypeAll <$-> token DotDot
>            <|> flip ExportTypeWith <$> con `sepBy` comma

> moduleDecls :: Parser Token ([ImportDecl],[TopDecl ()]) a
> moduleDecls = impDecl <$> importDecl
>                       <*> (semicolon <-*> moduleDecls `opt` ([],[]))
>           <|> (,) [] <$> topDecl `sepBy` semicolon
>   where impDecl i (is,ds) = (i:is,ds)

> importDecl :: Parser Token ImportDecl a
> importDecl =
>   flip . ImportDecl <$> position <*-> token KW_import 
>                     <*> (True <$-> token Id_qualified `opt` False)
>                     <*> mIdent
>                     <*> (Just <$-> token Id_as <*> mIdent `opt` Nothing)
>                     <*> (Just <$> importSpec `opt` Nothing)

> importSpec :: Parser Token ImportSpec a
> importSpec = position <**> (Hiding <$-> token Id_hiding `opt` Importing)
>                       <*> parens (spec `sepBy` comma)
>   where spec = tycon <**> (parens constrs `opt` Import)
>            <|> Import <$> fun <\> tycon
>         constrs = ImportTypeAll <$-> token DotDot
>               <|> flip ImportTypeWith <$> con `sepBy` comma

\end{verbatim}
If a source module has no explicit module header, the compiler
substitutes a default module header \texttt{module} $M$
\texttt{where} if the module is saved in file $M$\texttt{.curry}. The
directory path to the module is ignored.
\begin{verbatim}

> defaultMIdent :: FilePath -> ModuleIdent
> defaultMIdent fn = mkMIdent [rootname (basename fn)]

\end{verbatim}
\paragraph{Interfaces}
\begin{verbatim}

> parseInterface :: FilePath -> String -> Error Interface
> parseInterface fn s = applyParser parseIntf lexer fn s

> parseIntf :: Parser Token Interface a
> parseIntf = uncurry <$> intfHeader <*> braces intfDecls

> intfHeader :: Parser Token ([IImportDecl] -> [IDecl] -> Interface) a
> intfHeader = Interface <$-> token Id_interface <*> moduleName
>                        <*-> (token KW_where <?> "where expected")
>   where moduleName = mIdent
>                  <|> mkMIdent . return <$> string
>                  <?> "module name expected"

> intfDecls :: Parser Token ([IImportDecl],[IDecl]) a
> intfDecls = impDecl <$> iImportDecl
>                     <*> (semicolon <-*> intfDecls `opt` ([],[]))
>         <|> (,) [] <$> intfDecl `sepBy` semicolon
>   where impDecl i (is,ds) = (i:is,ds)

> iImportDecl :: Parser Token IImportDecl a
> iImportDecl = IImportDecl <$> position <*-> token KW_import <*> mIdent

\end{verbatim}
\paragraph{Goals}
\begin{verbatim}

> parseGoal :: String -> Error (Goal ())
> parseGoal s = applyParser goal lexer "" s

> goal :: Parser Token (Goal ()) a
> goal = Goal <$> position <*> expr <*> localDefs

\end{verbatim}
\paragraph{Declarations}
\begin{verbatim}

> topDecl :: Parser Token (TopDecl ()) a
> topDecl = dataDecl <|> newtypeDecl <|> typeDecl
>       <|> classDecl <|> instanceDecl <|> BlockDecl <$> blockDecl
>   where blockDecl = infixDecl <|> functionDecl <|> foreignDecl
>                 <|> trustAnnotation

> localDefs :: Parser Token [Decl ()] a
> localDefs = token KW_where <-*> layout valueDecls
>       `opt` []

> valueDecls :: Parser Token [Decl ()] a
> valueDecls = localDecl `sepBy` semicolon
>   where localDecl = infixDecl <|> valueDecl <|> foreignDecl
>                 <|> trustAnnotation

> dataDecl :: Parser Token (TopDecl ()) a
> dataDecl = dataDeclLhs DataDecl KW_data <*> constrs <*> deriv
>   where constrs = equals <-*> constrDecl `sepBy1` bar
>             `opt` []

> newtypeDecl :: Parser Token (TopDecl ()) a
> newtypeDecl =
>   dataDeclLhs NewtypeDecl KW_newtype <*-> equals <*> newConstrDecl <*> deriv

> typeDecl :: Parser Token (TopDecl ()) a
> typeDecl = typeDeclLhs (uncurry . TypeDecl) KW_type id <*-> equals <*> type0

> dataDeclLhs :: (Position -> [ClassAssert] -> Ident -> [Ident] -> a)
>             -> Category -> Parser Token a b
> dataDeclLhs f kw = typeDeclLhs f' kw (withContext (,))
>   where f' p = uncurry (uncurry . f p)

> typeDeclLhs :: (Position -> a -> b) -> Category
>             -> (Parser Token (Ident,[Ident]) c -> Parser Token a c)
>             -> Parser Token b c
> typeDeclLhs f kw g =
>   f <$> position <*-> token kw <*> g ((,) <$> tycon <*> many typeVar)
>   where typeVar = tyvar <|> anonId <$-> token Underscore

> constrDecl :: Parser Token ConstrDecl a
> constrDecl = position <**> (existVars <**> constr)
>   where existVars = token Id_forall <-*> many1 tyvar <*-> dot `opt` []
>         constr = conId <**> identDecl
>              <|> leftParen <-*> parenDecl
>              <|> type1 <\> conId <\> leftParen <**> opDecl
>         identDecl = many type2 <**> (conType <$> opDecl `opt` conDecl)
>         parenDecl = flip conDecl <$> conSym <*-> rightParen <*> many type2
>                 <|> applyType <$> parenType <*-> rightParen <*> many type2
>                               <**> opDecl
>         parenType = tupleType <|> ConstructorType <$> gtyconId
>         opDecl = conOpDecl <$> conop <*> type1
>         conType f tys c = f (applyType (ConstructorType (qualify c)) tys)
>         conDecl tys c tvs p = ConstrDecl p tvs c tys
>         conOpDecl op ty2 ty1 tvs p = ConOpDecl p tvs ty1 op ty2
>         applyType = foldl ApplyType

> newConstrDecl :: Parser Token NewConstrDecl a
> newConstrDecl = NewConstrDecl <$> position <*> con <*> type2

> deriv :: Parser Token [QualIdent] a
> deriv = token KW_deriving <-*> classes
>   `opt` []
>   where classes = return <$> qtycls
>               <|> parens (qtycls `sepBy` comma)

> classDecl :: Parser Token (TopDecl ()) a
> classDecl = classInstDecl ClassDecl KW_class tycls tyvar classMethod
>   where classMethod = methodFixity <|> methodSig <|?> methodDecl
>                   <|> trustMethod

> instanceDecl :: Parser Token (TopDecl ()) a
> instanceDecl = classInstDecl InstanceDecl KW_instance qtycls type2 instMethod
>   where instMethod = methodDecl <|> trustMethod

> classInstDecl :: (Position -> [ClassAssert] -> a -> b -> [c] -> TopDecl ())
>               -> Category -> Parser Token a d -> Parser Token b d
>               -> Parser Token c d -> Parser Token (TopDecl ()) d
> classInstDecl f kw cls ty d =
>   f' <$> position <*> classInstHead kw cls ty <*> methodDefs d
>   where methodDefs d = token KW_where <-*> layout (d `sepBy` semicolon)
>                  `opt` []
>         f' p = uncurry (uncurry . f p)

> classInstHead :: Category -> Parser Token a c -> Parser Token b c
>               -> Parser Token ([ClassAssert],(a,b)) c
> classInstHead kw cls ty = token kw <-*> withContext (,) ((,) <$> cls <*> ty)
>   -- NB Don't try to ``optimize'' this into withContext (,,) cls <*> ty
>   --    as this will yield a parse error if the context is omitted

> methodFixity :: Parser Token (MethodDecl ()) a
> methodFixity = infixDeclLhs MethodFixity <*> funop `sepBy1` comma

> methodSig :: Parser Token (MethodDecl ()) a
> methodSig =
>   MethodSig <$> position <*> var `sepBy1` comma
>             <*-> token DoubleColon <*> qualType

> methodDecl :: Parser Token (MethodDecl ()) a
> methodDecl = methodDecl <$> position <*> lhs <*> declRhs
>   where lhs = (\f -> (f,FunLhs f [])) <$> fun
>          <|?> funLhs
>         methodDecl p (f,lhs) rhs = MethodDecl p f [Equation p lhs rhs]

> trustMethod :: Parser Token (MethodDecl ()) a
> trustMethod =
>   TrustMethod <$> position <*> tokenOps pragmaKW <*> funList
>               <*-> token PragmaEnd
>   where pragmaKW = [(PragmaBegin SuspectPragma,Suspect),
>                     (PragmaBegin TrustPragma,Trust)]
>         funList = Nothing <$-> token Underscore
>               <|> Just <$> fun `sepBy1` comma

> infixDecl :: Parser Token (Decl ()) a
> infixDecl = infixDeclLhs InfixDecl <*> funop `sepBy1` comma

> infixDeclLhs :: (Position -> Infix -> Int -> a) -> Parser Token a b
> infixDeclLhs f = f <$> position <*> tokenOps infixKW <*> int
>   where infixKW = [(KW_infix,Infix),(KW_infixl,InfixL),(KW_infixr,InfixR)]

> functionDecl :: Parser Token (Decl ()) a
> functionDecl = position <**> decl
>   where decl = fun `sepBy1` comma <**> funListDecl
>           <|?> funDecl <$> lhs <*> declRhs
>         lhs = (\f -> (f,FunLhs f [])) <$> fun
>          <|?> funLhs

> valueDecl :: Parser Token (Decl ()) a
> valueDecl = position <**> decl
>   where decl = var `sepBy1` comma <**> valListDecl
>           <|?> valDecl <$> constrTerm0 <*> declRhs
>           <|?> funDecl <$> curriedLhs <*> declRhs
>         valDecl (ConstructorPattern _ c ts)
>           | not (isConstrId c) = funDecl (f,FunLhs f ts)
>           where f = unqualify c
>         valDecl t = opDecl id t
>         opDecl f (InfixPattern _ t1 op t2)
>           | isConstrId op = opDecl (f . InfixPattern () t1 op) t2
>           | otherwise = funDecl (op',OpLhs (f t1) op' t2)
>           where op' = unqualify op
>         opDecl f t = patDecl (f t)
>         isConstrId c = c == qConsId || isQualified c || isQTupleId c

> funDecl :: (Ident,Lhs a) -> Rhs a -> Position -> Decl a
> funDecl (f,lhs) rhs p = FunctionDecl p f [Equation p lhs rhs]

> patDecl :: ConstrTerm a -> Rhs a -> Position -> Decl a
> patDecl t rhs p = PatternDecl p t rhs

> funListDecl :: Parser Token ([Ident] -> Position -> Decl ()) a
> funListDecl = typeSig <$-> token DoubleColon <*> qualType
>   where typeSig ty vs p = TypeSig p vs ty

> valListDecl :: Parser Token ([Ident] -> Position -> Decl ()) a
> valListDecl = funListDecl
>           <|> flip FreeDecl <$-> token KW_free

> funLhs :: Parser Token (Ident,Lhs ()) a
> funLhs = funLhs <$> fun <*> many1 constrTerm2
>     <|?> flip ($ id) <$> constrTerm1 <*> opLhs'
>     <|?> curriedLhs
>   where opLhs' = opLhs <$> funSym <*> constrTerm0
>              <|> infixPat <$> gConSym <\> funSym <*> constrTerm1 <*> opLhs'
>              <|> backquote <-*> opIdLhs
>         opIdLhs = opLhs <$> funId <*-> checkBackquote <*> constrTerm0
>               <|> infixPat <$> qConId <\> funId <*-> backquote <*> constrTerm1
>                            <*> opLhs'
>         funLhs f ts = (f,FunLhs f ts)
>         opLhs op t2 f t1 = (op,OpLhs (f t1) op t2)
>         infixPat op t2 f g t1 = f (g . InfixPattern () t1 op) t2

> curriedLhs :: Parser Token (Ident,Lhs ()) a
> curriedLhs = apLhs <$> parens funLhs <*> many1 constrTerm2
>   where apLhs (f,lhs) ts = (f,ApLhs lhs ts)

> declRhs :: Parser Token (Rhs ()) a
> declRhs = rhs equals

> rhs :: Parser Token a b -> Parser Token (Rhs ()) b
> rhs eq = rhsExpr <*> localDefs
>   where rhsExpr = SimpleRhs <$-> eq <*> position <*> expr
>               <|> GuardedRhs <$> many1 (condExpr eq)

> foreignDecl :: Parser Token (Decl ()) a
> foreignDecl =
>   mkDecl <$> position <*-> token KW_foreign <*-> token KW_import
>          <*> callConv <*> safeEntity <*-> token DoubleColon <*> type0
>   where mkDecl p cc (ie,f) ty = ForeignDecl p cc ie f ty
>         callConv = CallConvPrimitive <$-> token Id_primitive
>                <|> CallConvCCall <$-> token Id_ccall
>         safeEntity = safety <**> (const <$> importEntity `opt` safetyId)
>                  <|> importEntity <\> safety
>         importEntity = (,) <$> (Just <$> string `opt` Nothing) <*> fun
>         safety = tokens [Id_safe,Id_unsafe]
>         safetyId x = (Nothing,mkIdent (sval x))

> trustAnnotation :: Parser Token (Decl ()) a
> trustAnnotation =
>   TrustAnnot <$> position <*> tokenOps pragmaKW <*> funList
>              <*-> token PragmaEnd
>   where pragmaKW = [(PragmaBegin SuspectPragma,Suspect),
>                     (PragmaBegin TrustPragma,Trust)]
>         funList = Nothing <$-> token Underscore
>               <|> Just <$> fun `sepBy1` comma

\end{verbatim}
\paragraph{Interface declarations}
\begin{verbatim}

> intfDecl :: Parser Token IDecl a
> intfDecl = iInfixDecl
>        <|> iHidingDecl <|> iDataDecl <|> iNewtypeDecl <|> iTypeDecl
>        <|> iClassDecl <|> iInstanceDecl <|> iFunctionDecl <\> token Id_hiding

> iInfixDecl :: Parser Token IDecl a
> iInfixDecl = infixDeclLhs IInfixDecl <*> qfunop

> iHidingDecl :: Parser Token IDecl a
> iHidingDecl =
>   position <*-> token Id_hiding <**> (dataDecl <|> classDecl <|> funcDecl)
>   where dataDecl =
>           hidingData <$-> token KW_data <*> withKind qtycon <*> many tyvar
>         classDecl =
>           hidingClass <$> classInstHead KW_class (withKind qtycls) tyvar
>         funcDecl = hidingFunc <$-> token DoubleColon <*> qualType
>         hidingData (tc,k) tvs p = HidingDataDecl p tc k tvs
>         hidingClass (cx,((cls,k),tv)) p = HidingClassDecl p cx cls k tv
>         hidingFunc ty p = IFunctionDecl p hidingId ty
>         hidingId = qualify (mkIdent "hiding")

> iDataDecl :: Parser Token IDecl a
> iDataDecl = iDataDeclLhs IDataDecl KW_data <*> constrs
>   where constrs = equals <-*> maybeHidden constrDecl `sepBy1` bar
>             `opt` []

> maybeHidden :: Parser Token a b -> Parser Token (Maybe a) b
> maybeHidden p = Just <$> p <\> token Underscore
>             <|> Nothing <$-> token Underscore

> iNewtypeDecl :: Parser Token IDecl a
> iNewtypeDecl =
>   iDataDeclLhs INewtypeDecl KW_newtype <*-> equals <*> newConstrDecl

> iTypeDecl :: Parser Token IDecl a
> iTypeDecl = iTypeDeclLhs typeDecl KW_type id <*-> equals <*> type0
>   where typeDecl = uncurry . uncurry . ITypeDecl

> iDataDeclLhs :: (Position -> [ClassAssert] -> QualIdent -> Maybe KindExpr
>                  -> [Ident] -> a)
>              -> Category -> Parser Token a b
> iDataDeclLhs f kw = iTypeDeclLhs f' kw (withContext (,))
>   where f' p = uncurry (uncurry . uncurry . f p)

> iTypeDeclLhs :: (Position -> a -> b) -> Category
>              -> (Parser Token ((QualIdent,Maybe KindExpr),[Ident]) c
>                  -> Parser Token a c)
>              -> Parser Token b c
> iTypeDeclLhs f kw g =
>   f <$> position <*-> token kw <*> g ((,) <$> withKind qtycon <*> many tyvar)

> iClassDecl :: Parser Token IDecl a
> iClassDecl =
>   iClassInstDecl classDecl KW_class (withKind qtycls) tyvar <*> methodDefs
>   where classDecl p = uncurry . IClassDecl p
>         methodDefs = token KW_where <-*> braces (methodDecl `sepBy` semicolon)
>                `opt` []
>         methodDecl = maybeHidden iMethodDecl

> iInstanceDecl :: Parser Token IDecl a
> iInstanceDecl = iClassInstDecl IInstanceDecl KW_instance qtycls type2

> iClassInstDecl :: (Position -> [ClassAssert] -> a -> b -> c) -> Category
>                -> Parser Token a d -> Parser Token b d -> Parser Token c d
> iClassInstDecl f kw cls ty = f' <$> position <*> classInstHead kw cls ty
>   where f' p = uncurry (uncurry . f p)

> iFunctionDecl :: Parser Token IDecl a
> iFunctionDecl = iFunDecl IFunctionDecl qfun

> iMethodDecl :: Parser Token IMethodDecl a
> iMethodDecl = iFunDecl IMethodDecl fun

> iFunDecl :: (Position -> a -> QualTypeExpr -> b) -> Parser Token a c
>          -> Parser Token b c
> iFunDecl f fun = f <$> position <*> fun <*-> token DoubleColon <*> qualType

\end{verbatim}
\paragraph{Kinds}
\begin{verbatim}

> withKind :: Parser Token a b -> Parser Token (a,Maybe KindExpr) b
> withKind p = implicitKind <$> p
>          <|> parens (explicitKind <$> p <*-> token DoubleColon <*> kind0)
>   where implicitKind x = (x,Nothing)
>         explicitKind x k = (x,Just k)

> kind0 :: Parser Token KindExpr a
> kind0 = kind1 `chainr1` (ArrowKind <$-> token RightArrow)

> kind1 :: Parser Token KindExpr a
> kind1 = Star <$-> token Sym_Star
>     <|> parens kind0

\end{verbatim}
\paragraph{Types}
\begin{verbatim}

> qualType :: Parser Token QualTypeExpr a
> qualType = withContext QualTypeExpr type0

> withContext :: ([ClassAssert] -> a -> b) -> Parser Token a c
>             -> Parser Token b c
> withContext f p = f <$> context <*-> token DoubleRightArrow <*> p
>              <|?> f [] <$> p

> context :: Parser Token [ClassAssert] a
> context = return <$> classAssert
>       <|> parens (classAssert `sepBy` comma)

> classAssert :: Parser Token ClassAssert a
> classAssert = ClassAssert <$> qtycls <*> tyvar

> type0 :: Parser Token TypeExpr a
> type0 = type1 `chainr1` (ArrowType <$-> token RightArrow)

> type1 :: Parser Token TypeExpr a
> type1 = foldl ApplyType <$> type2 <*> many type2

> type2 :: Parser Token TypeExpr a
> type2 = anonType <|> identType <|> parenType <|> listType

> anonType :: Parser Token TypeExpr a
> anonType = VariableType anonId <$-> token Underscore

> identType :: Parser Token TypeExpr a
> identType = VariableType <$> tyvar
>         <|> ConstructorType <$> qtycon <\> tyvar

> parenType :: Parser Token TypeExpr a
> parenType = parens (tupleType <|> ConstructorType <$> gtyconId)

> tupleType :: Parser Token TypeExpr a
> tupleType = type0 <??> (tuple <$> many1 (comma <-*> type0))
>       `opt` ConstructorType qUnitId
>   where tuple tys ty = TupleType (ty:tys)

> listType :: Parser Token TypeExpr a
> listType = brackets (ListType <$> type0 `opt` ConstructorType qListId)

> gtyconId :: Parser Token QualIdent a
> gtyconId = rightArrow <|> tupleCommas

\end{verbatim}
\paragraph{Literals}
\begin{verbatim}

> literal :: Parser Token Literal a
> literal = Char <$> char
>       <|> Int <$> int
>       <|> Float <$> float
>       <|> String <$> string

\end{verbatim}
\paragraph{Patterns}
\begin{verbatim}

> constrTerm0 :: Parser Token (ConstrTerm ()) a
> constrTerm0 = constrTerm1 `chainr1` (flip (InfixPattern ()) <$> gconop)

> constrTerm1 :: Parser Token (ConstrTerm ()) a
> constrTerm1 = varId <**> identPattern
>           <|> constrPattern (qConId <\> varId)
>           <|> minus <-*> negLit
>           <|> leftParen <-*> parenPattern
>           <|> constrTerm2 <\> qConId <\> leftParen
>   where identPattern = optAsPattern
>                    <|> conPattern <$> many1 constrTerm2
>         constrPattern p = ConstructorPattern () <$> p <*> many constrTerm2
>         parenPattern = minus <**> minusPattern
>                    <|> gconPattern
>                    <|> funSym <\> minus <*-> rightParen <**> identPattern
>                    <|> parenTuplePattern <\> minus <*-> rightParen
>         minusPattern = rightParen <-*> identPattern
>                    <|> parenMinusPattern <*-> rightParen
>         gconPattern = constrPattern (gconId <*-> rightParen)
>         conPattern ts = flip (ConstructorPattern ()) ts . qualify

> constrTerm2 :: Parser Token (ConstrTerm ()) a
> constrTerm2 = literalPattern <|> anonPattern <|> identPattern
>           <|> parenPattern <|> listPattern <|> lazyPattern

> literalPattern :: Parser Token (ConstrTerm ()) a
> literalPattern = LiteralPattern () <$> literal

> anonPattern :: Parser Token (ConstrTerm ()) a
> anonPattern = VariablePattern () anonId <$-> token Underscore

> identPattern :: Parser Token (ConstrTerm ()) a
> identPattern = varId <**> optAsPattern
>            <|> flip (ConstructorPattern ()) [] <$> qConId <\> varId

> parenPattern :: Parser Token (ConstrTerm ()) a
> parenPattern = leftParen <-*> parenPattern
>   where parenPattern = minus <**> minusPattern
>                    <|> flip (ConstructorPattern ()) [] <$> gconId
>                                                        <*-> rightParen
>                    <|> funSym <\> minus <*-> rightParen <**> optAsPattern
>                    <|> parenTuplePattern <\> minus <*-> rightParen
>         minusPattern = rightParen <-*> optAsPattern
>                    <|> parenMinusPattern <*-> rightParen

> listPattern :: Parser Token (ConstrTerm ()) a
> listPattern = ListPattern () <$> brackets (constrTerm0 `sepBy` comma)

> lazyPattern :: Parser Token (ConstrTerm ()) a
> lazyPattern = LazyPattern <$-> token Tilde <*> constrTerm2

\end{verbatim}
Partial patterns used in the combinators above, but also for parsing
the left-hand side of a declaration.
\begin{verbatim}

> gconId :: Parser Token QualIdent a
> gconId = colon <|> tupleCommas

> negLit :: Parser Token (ConstrTerm ()) a
> negLit = NegativePattern () <$> (Int <$> int <|> Float <$> float)

> optAsPattern :: Parser Token (Ident -> ConstrTerm ()) a
> optAsPattern = flip AsPattern <$-> token At <*> constrTerm2
>          `opt` VariablePattern ()

> optInfixPattern :: Parser Token (ConstrTerm () -> ConstrTerm ()) a
> optInfixPattern = infixPat <$> gconop <*> constrTerm0
>             `opt` id
>   where infixPat op t2 t1 = InfixPattern () t1 op t2

> optTuplePattern :: Parser Token (ConstrTerm () -> ConstrTerm ()) a
> optTuplePattern = tuple <$> many1 (comma <-*> constrTerm0)
>             `opt` ParenPattern
>   where tuple ts t = TuplePattern (t:ts)

> parenMinusPattern :: Parser Token (Ident -> ConstrTerm ()) a
> parenMinusPattern = const <$> negLit <.> optInfixPattern <.> optTuplePattern

> parenTuplePattern :: Parser Token (ConstrTerm ()) a
> parenTuplePattern = constrTerm0 <**> optTuplePattern
>               `opt` ConstructorPattern () qUnitId []

\end{verbatim}
\paragraph{Expressions}
\begin{verbatim}

> condExpr :: Parser Token a b -> Parser Token (CondExpr ()) b
> condExpr eq = CondExpr <$> position <*-> bar <*> expr0 <*-> eq <*> expr

> expr :: Parser Token (Expression ()) a
> expr = expr0 <??> (flip Typed <$-> token DoubleColon <*> qualType)

> expr0 :: Parser Token (Expression ()) a
> expr0 = expr1 `chainr1` (flip InfixApply <$> infixOp)

> expr1 :: Parser Token (Expression ()) a
> expr1 = UnaryMinus <$-> minus <*> expr2
>     <|> expr2

> expr2 :: Parser Token (Expression ()) a
> expr2 = lambdaExpr <|> letExpr <|> doExpr <|> ifExpr <|> caseExpr
>     <|> foldl1 Apply <$> many1 expr3

> expr3 :: Parser Token (Expression ()) a
> expr3 = constant <|> variable <|> parenExpr <|> listExpr

> constant :: Parser Token (Expression ()) a
> constant = Literal () <$> literal

> variable :: Parser Token (Expression ()) a
> variable = Variable () <$> qFunId

> parenExpr :: Parser Token (Expression ()) a
> parenExpr = parens pExpr
>   where pExpr = minus <**> minusOrTuple
>             <|> Constructor () <$> tupleCommas
>             <|> leftSectionOrTuple <\> minus
>             <|> opOrRightSection <\> minus
>           `opt` Constructor () qUnitId
>         minusOrTuple = const . UnaryMinus <$> expr1 <.> infixOrTuple
>                  `opt` Variable () . qualify
>         leftSectionOrTuple = expr1 <**> infixOrTuple
>         infixOrTuple = ($ id) <$> infixOrTuple'
>         infixOrTuple' = infixOp <**> leftSectionOrExp
>                     <|> (.) <$> (optType <.> tupleExpr)
>         leftSectionOrExp = expr1 <**> (infixApp <$> infixOrTuple')
>                      `opt` leftSection
>         optType = flip Typed <$-> token DoubleColon <*> qualType
>             `opt` id
>         tupleExpr = tuple <$> many1 (comma <-*> expr)
>               `opt` Paren
>         opOrRightSection = qFunSym <**> optRightSection InfixOp Variable
>                        <|> colon <**> optRightSection InfixConstr Constructor
>                        <|> infixOp <\> colon <\> qFunSym <**> rightSection
>         optRightSection op var = (. op ()) <$> rightSection `opt` var ()
>         rightSection = flip RightSection <$> expr0
>         infixApp f e2 op g e1 = f (g . InfixApply e1 op) e2
>         leftSection op f e = LeftSection (f e) op
>         tuple es e = Tuple (e:es)

> infixOp :: Parser Token (InfixOp ()) a
> infixOp = InfixOp () <$> qfunop
>       <|> InfixConstr () <$> colon

> listExpr :: Parser Token (Expression ()) a
> listExpr = brackets (elements `opt` List () [])
>   where elements = expr <**> rest
>         rest = comprehension
>            <|> enumeration (flip EnumFromTo) EnumFrom
>            <|> comma <-*> expr <**>
>                (enumeration (flip3 EnumFromThenTo) (flip EnumFromThen)
>                <|> (\es e2 e1 -> List () (e1:e2:es)) <$>
>                    many (comma <-*> expr))
>          `opt` (\e -> List () [e])
>         comprehension = flip ListCompr <$-> bar <*> quals
>         enumeration enumTo enum =
>           token DotDot <-*> (enumTo <$> expr `opt` enum)
>         flip3 f x y z = f z y x

> lambdaExpr :: Parser Token (Expression ()) a
> lambdaExpr = Lambda <$-> token Backslash <*> many1 constrTerm2
>                     <*-> (token RightArrow <?> "-> expected") <*> expr

> letExpr :: Parser Token (Expression ()) a
> letExpr = Let <$-> token KW_let <*> layout valueDecls
>               <*-> (token KW_in <?> "in expected") <*> expr

> doExpr :: Parser Token (Expression ()) a
> doExpr = uncurry Do <$-> token KW_do <*> layout stmts

> ifExpr :: Parser Token (Expression ()) a
> ifExpr = IfThenElse <$-> token KW_if <*> expr
>                     <*-> (token KW_then <?> "then expected") <*> expr
>                     <*-> (token KW_else <?> "else expected") <*> expr

> caseExpr :: Parser Token (Expression ()) a
> caseExpr = Case <$-> token KW_case <*> expr
>                 <*-> (token KW_of <?> "of expected") <*> layout alts

> alts :: Parser Token [Alt ()] a
> alts = alt `sepBy1` semicolon

> alt :: Parser Token (Alt ()) a
> alt = Alt <$> position <*> constrTerm0
>           <*> rhs (token RightArrow <?> "-> expected")

\end{verbatim}
\paragraph{Statements in list comprehensions and \texttt{do} expressions}
Parsing statements is a bit difficult because the syntax of patterns
and expressions largely overlaps. The parser will first try to
recognize the prefix \emph{Pattern}~\texttt{<-} of a binding statement
and if this fails fall back into parsing an expression statement. In
addition, we have to be prepared that the sequence
\texttt{let}~\emph{LocalDefs} can be either a let-statement or the
prefix of a let expression.
\begin{verbatim}

> stmts :: Parser Token ([Statement ()],Expression ()) a
> stmts = stmt reqStmts optStmts

> reqStmts :: Parser Token (Statement () -> ([Statement ()],Expression ())) a
> reqStmts = (\(sts,e) st -> (st : sts,e)) <$-> semicolon <*> stmts

> optStmts :: Parser Token (Expression () -> ([Statement ()],Expression ())) a
> optStmts = succeed StmtExpr <.> reqStmts
>      `opt` (,) []

> quals :: Parser Token [Statement ()] a
> quals = stmt (succeed id) (succeed StmtExpr) `sepBy1` comma

> stmt :: Parser Token (Statement () -> a) b
>      -> Parser Token (Expression () -> a) b
>      -> Parser Token a b
> stmt stmtCont exprCont = letStmt stmtCont exprCont
>                      <|> exprOrBindStmt stmtCont exprCont

> letStmt :: Parser Token (Statement () -> a) b
>         -> Parser Token (Expression () -> a) b
>         -> Parser Token a b
> letStmt stmtCont exprCont = token KW_let <-*> layout valueDecls <**> optExpr
>   where optExpr = flip Let <$-> token KW_in <*> expr <.> exprCont
>               <|> succeed StmtDecl <.> stmtCont

> exprOrBindStmt :: Parser Token (Statement () -> a) b
>                -> Parser Token (Expression () -> a) b
>                -> Parser Token a b
> exprOrBindStmt stmtCont exprCont =
>        StmtBind <$> constrTerm0 <*-> leftArrow <*> expr <**> stmtCont
>   <|?> expr <\> token KW_let <**> exprCont

\end{verbatim}
\paragraph{Literals, identifiers, and (infix) operators}
\begin{verbatim}

> char :: Parser Token Char a
> char = cval <$> token CharTok

> int, checkInt :: Parser Token Int a
> int = ival <$> token IntTok
> checkInt = int <?> "integer number expected"

> float, checkFloat :: Parser Token Double a
> float = fval <$> token FloatTok
> checkFloat = float <?> "floating point number expected"

> string :: Parser Token String a
> string = sval <$> token StringTok

> tycon, tycls, tyvar :: Parser Token Ident a
> tycon = conId
> tycls = conId
> tyvar = varId

> qtycon,qtycls :: Parser Token QualIdent a
> qtycon = qConId
> qtycls = qConId

> varId, funId, conId :: Parser Token Ident a
> varId = ident
> funId = ident
> conId = ident

> funSym, conSym :: Parser Token Ident a
> funSym = sym
> conSym = sym

> var, fun, con :: Parser Token Ident a
> var = varId <|> parens (funSym <?> "operator symbol expected")
> fun = funId <|> parens (funSym <?> "operator symbol expected")
> con = conId <|> parens (conSym <?> "operator symbol expected")

> funop, conop :: Parser Token Ident a
> funop = funSym <|> backquotes (funId <?> "operator name expected")
> conop = conSym <|> backquotes (conId <?> "operator name expected")

> qFunId, qConId :: Parser Token QualIdent a
> qFunId = qIdent
> qConId = qIdent

> qFunSym, qConSym :: Parser Token QualIdent a
> qFunSym = qSym
> qConSym = qSym
> gConSym = qConSym <|> colon

> qfun, qcon :: Parser Token QualIdent a
> qfun = qFunId <|> parens (qFunSym <?> "operator symbol expected")
> qcon = qConId <|> parens (qConSym <?> "operator symbol expected")

> qfunop, qconop, gconop :: Parser Token QualIdent a
> qfunop = qFunSym <|> backquotes (qFunId <?> "operator name expected")
> qconop = qConSym <|> backquotes (qConId <?> "operator name expected")
> gconop = gConSym <|> backquotes (qConId <?> "operator name expected")

> specialIdents, specialSyms :: [Category]
> specialIdents = [Id_as,Id_ccall,Id_forall,Id_hiding,Id_interface,
>                  Id_primitive,Id_qualified,Id_safe,Id_unsafe]
> specialSyms = [Sym_Dot,Sym_Minus,Sym_Star]

> ident :: Parser Token Ident a
> ident = mkIdent . sval <$> tokens (Id : specialIdents)

> qIdent :: Parser Token QualIdent a
> qIdent = qualify <$> ident <|> mkQIdent <$> token QId
>   where mkQIdent a = qualifyWith (mkMIdent (modul a)) (mkIdent (sval a))

> mIdent :: Parser Token ModuleIdent a
> mIdent = mIdent <$> tokens (Id : QId : specialIdents)
>   where mIdent a = mkMIdent (modul a ++ [sval a])

> sym :: Parser Token Ident a
> sym = mkIdent . sval <$> tokens (Sym : specialSyms)

> qSym :: Parser Token QualIdent a
> qSym = qualify <$> sym <|> mkQIdent <$> token QSym
>   where mkQIdent a = qualifyWith (mkMIdent (modul a)) (mkIdent (sval a))

> colon :: Parser Token QualIdent a
> colon = qConsId <$-> token Colon

> rightArrow :: Parser Token QualIdent a
> rightArrow = qArrowId <$-> token RightArrow

> minus :: Parser Token Ident a
> minus = minusId <$-> token Sym_Minus

> tupleCommas :: Parser Token QualIdent a
> tupleCommas = qTupleId . (1 + ) . length <$> many1 comma

\end{verbatim}
\paragraph{Layout}
\begin{verbatim}

> layout :: Parser Token a b -> Parser Token a b
> layout p = layoutOff <-*> braces p
>        <|> layoutOn <-*> p <*-> (token VRightBrace <|> layoutEnd)

\end{verbatim}
\paragraph{More combinators}
\begin{verbatim}

> braces, brackets, parens, backquotes :: Parser Token a b -> Parser Token a b
> braces p = bracket leftBrace p rightBrace
> brackets p = bracket leftBracket p rightBracket
> parens p = bracket leftParen p rightParen
> backquotes p = bracket backquote p checkBackquote

\end{verbatim}
\paragraph{Simple token parsers}
\begin{verbatim}

> token :: Category -> Parser Token Attributes a
> token c = attr <$> symbol (Token c NoAttributes)
>   where attr (Token _ a) = a

> tokens :: [Category] -> Parser Token Attributes a
> tokens cs = foldr1 (<|>) (map token cs)

> tokenOps :: [(Category,a)] -> Parser Token a b
> tokenOps cs = ops [(Token c NoAttributes,x) | (c,x) <- cs]

> dot, comma, semicolon, bar, equals :: Parser Token Attributes a
> dot = token Sym_Dot
> comma = token Comma
> semicolon = token Semicolon <|> token VSemicolon
> bar = token Bar
> equals = token Equals

> backquote, checkBackquote :: Parser Token Attributes a
> backquote = token Backquote
> checkBackquote = backquote <?> "backquote (`) expected"

> leftParen, rightParen :: Parser Token Attributes a
> leftParen = token LeftParen
> rightParen = token RightParen

> leftBracket, rightBracket :: Parser Token Attributes a
> leftBracket = token LeftBracket
> rightBracket = token RightBracket

> leftBrace, rightBrace :: Parser Token Attributes a
> leftBrace = token LeftBrace
> rightBrace = token RightBrace

> leftArrow :: Parser Token Attributes a
> leftArrow = token LeftArrow

\end{verbatim}
