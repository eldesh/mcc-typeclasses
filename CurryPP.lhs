% -*- LaTeX -*-
% $Id: CurryPP.lhs 1995 2006-11-10 14:27:14Z wlux $
%
% Copyright (c) 1999-2006, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CurryPP.lhs}
\section{A Pretty Printer for Curry}\label{sec:CurryPP}
This module implements a pretty printer for Curry expressions. It was
derived from the Haskell pretty printer provided in Simon Marlow's
Haskell parser.
\begin{verbatim}

> module CurryPP(module CurryPP, Doc) where
> import Ident
> import CurrySyntax
> import Char
> import Pretty

\end{verbatim}
Pretty print a module
\begin{verbatim}

> ppModule :: Module a -> Doc
> ppModule (Module m es is ds) =
>   vcat (ppModuleHeader m es : map ppImportDecl is ++ map ppTopDecl ds)

\end{verbatim}
Module header
\begin{verbatim}

> ppModuleHeader :: ModuleIdent -> Maybe ExportSpec -> Doc
> ppModuleHeader m es =
>   text "module" <+> ppMIdent m <+> maybePP ppExportSpec es <+> text "where"

> ppExportSpec :: ExportSpec -> Doc
> ppExportSpec (Exporting _ es) = parenList (map ppExport es)

> ppExport :: Export -> Doc
> ppExport (Export x) = ppQIdent x
> ppExport (ExportTypeWith tc cs) = ppQIdent tc <> parenList (map ppIdent cs)
> ppExport (ExportTypeAll tc) = ppQIdent tc <> text "(..)"
> ppExport (ExportModule m) = text "module" <+> ppMIdent m

> ppImportDecl :: ImportDecl -> Doc
> ppImportDecl (ImportDecl _ m q asM is) =
>   text "import" <+> ppQualified q <+> ppMIdent m <+> maybePP ppAs asM
>                 <+> maybePP ppImportSpec is
>   where ppQualified q = if q then text "qualified" else empty
>         ppAs m = text "as" <+> ppMIdent m

> ppImportSpec :: ImportSpec -> Doc
> ppImportSpec (Importing _ is) = parenList (map ppImport is)
> ppImportSpec (Hiding _ is) = text "hiding" <+> parenList (map ppImport is)

> ppImport :: Import -> Doc
> ppImport (Import x) = ppIdent x
> ppImport (ImportTypeWith tc cs) = ppIdent tc <> parenList (map ppIdent cs)
> ppImport (ImportTypeAll tc) = ppIdent tc <> text "(..)"

\end{verbatim}
Declarations
\begin{verbatim}

> ppTopDecl :: TopDecl a -> Doc
> ppTopDecl (DataDecl _ tc tvs cs) =
>   sep (ppTypeDeclLhs "data" tc tvs :
>        map indent (zipWith (<+>) (equals : repeat vbar) (map ppConstr cs)))
> ppTopDecl (NewtypeDecl _ tc tvs nc) =
>   sep [ppTypeDeclLhs "newtype" tc tvs <+> equals,indent (ppNewConstr nc)]
> ppTopDecl (TypeDecl _ tc tvs ty) =
>   sep [ppTypeDeclLhs "type" tc tvs <+> equals,indent (ppTypeExpr 0 ty)]
> ppTopDecl (ClassDecl _ cls tv ds) =
>   ppClassInstDecl (ppTypeDeclLhs "class" cls [tv]) (map ppMethodSig ds)
> ppTopDecl (InstanceDecl _ cls ty ds) =
>   ppClassInstDecl (text "instance" <+> ppQIdent cls <+> ppTypeExpr 2 ty)
>                   (map ppMethodDecl ds)
> ppTopDecl (BlockDecl d) = ppDecl d

> ppTypeDeclLhs :: String -> Ident -> [Ident] -> Doc
> ppTypeDeclLhs kw tc tvs = text kw <+> ppIdent tc <+> hsep (map ppIdent tvs)

> ppConstr :: ConstrDecl -> Doc
> ppConstr (ConstrDecl _ tvs c tys) =
>   sep [ppExistVars tvs,ppIdent c <+> fsep (map (ppTypeExpr 2) tys)]
> ppConstr (ConOpDecl _ tvs ty1 op ty2) =
>   sep [ppExistVars tvs,ppTypeExpr 1 ty1,ppInfixOp op <+> ppTypeExpr 1 ty2]

> ppExistVars :: [Ident] -> Doc
> ppExistVars tvs
>   | null tvs = empty
>   | otherwise = text "forall" <+> hsep (map ppIdent tvs) <+> char '.'

> ppNewConstr :: NewConstrDecl -> Doc
> ppNewConstr (NewConstrDecl _ c ty) = ppIdent c <+> ppTypeExpr 2 ty

> ppClassInstDecl :: Doc -> [Doc] -> Doc
> ppClassInstDecl head ds
>   | null ds = head
>   | otherwise = head <+> text "where" $$ indent (vcat ds)

> ppMethodSig :: MethodSig -> Doc
> ppMethodSig (MethodSig p fs ty) = ppDecl (TypeSig p fs (QualTypeExpr [] ty))

> ppMethodDecl :: MethodDecl a -> Doc
> ppMethodDecl (MethodDecl p f eqs) = ppDecl (FunctionDecl p f eqs)

> ppBlock :: [Decl a] -> Doc
> ppBlock = vcat . map ppDecl

> ppDecl :: Decl a -> Doc
> ppDecl (InfixDecl _ fix p ops) = ppPrec fix p <+> list (map ppInfixOp ops)
> ppDecl (TypeSig _ fs ty) = ppIdentList fs <+> text "::" <+> ppQualTypeExpr ty
> ppDecl (FunctionDecl _ _ eqs) = vcat (map ppEquation eqs)
> ppDecl (ForeignDecl p cc ie f ty) =
>   sep [text "foreign import" <+> ppCallConv cc <+> maybePP (text . show) ie,
>        indent (ppDecl (TypeSig p [f] (QualTypeExpr [] ty)))]
>   where ppCallConv CallConvPrimitive = text "primitive"
>         ppCallConv CallConvCCall = text "ccall"
> ppDecl (PatternDecl _ t rhs) = ppRule (ppConstrTerm 0 t) equals rhs
> ppDecl (FreeDecl _ vs) = ppIdentList vs <+> text "free"
> ppDecl (TrustAnnot _ t fs) =
>   ppPragma (ppTrust t <+> maybe (char '_') ppIdentList fs)
>   where ppTrust Suspect = text "SUSPECT"
>         ppTrust Trust = text "TRUST"

> ppPragma :: Doc -> Doc
> ppPragma p = text "{-#" <+> p <+> text "#-}"

> ppPrec :: Infix -> Int -> Doc
> ppPrec fix p = ppAssoc fix <+> ppPrio p
>   where ppAssoc InfixL = text "infixl"
>         ppAssoc InfixR = text "infixr"
>         ppAssoc Infix = text "infix"
>         ppPrio p = if p < 0 then empty else int p

> ppEquation :: Equation a -> Doc
> ppEquation (Equation _ lhs rhs) = ppRule (ppLhs lhs) equals rhs

> ppLhs :: Lhs  a -> Doc
> ppLhs (FunLhs f ts) = ppIdent f <+> fsep (map (ppConstrTerm 2) ts)
> ppLhs (OpLhs t1 f t2) =
>   ppConstrTerm 1 t1 <+> ppInfixOp f <+> ppConstrTerm 1 t2
> ppLhs (ApLhs lhs ts) = parens (ppLhs lhs) <+> fsep (map (ppConstrTerm 2) ts)

> ppRule :: Doc -> Doc -> Rhs a -> Doc
> ppRule lhs eq (SimpleRhs _ e ds) =
>   sep [lhs <+> eq,indent (ppExpr 0 e)] $$ ppLocalDefs ds
> ppRule lhs eq (GuardedRhs es ds) =
>   sep [lhs,indent (vcat (map (ppCondExpr eq) es))] $$ ppLocalDefs ds

> ppLocalDefs :: [Decl a] -> Doc
> ppLocalDefs ds
>   | null ds = empty
>   | otherwise = indent (text "where" <+> ppBlock ds)

\end{verbatim}
Interfaces
\begin{verbatim}

> ppInterface :: Interface -> Doc
> ppInterface (Interface m is ds) =
>   ppIBlock (text "interface" <+> ppModuleIdent m)
>            (map ppIImportDecl is ++ map ppIDecl ds)
>   where ppModuleIdent m
>           | isMIdent m = ppMIdent m
>           | otherwise = text (show (moduleName m))
>         isMIdent m = not (null ms) && all isIdent ms
>           where ms = moduleQualifiers m
>         isIdent "" = False
>         isIdent (c:cs) = isAlpha c && all isAlphaNum_ cs
>         isAlphaNum_ c = isAlphaNum c || c == '_'

> ppIImportDecl :: IImportDecl -> Doc
> ppIImportDecl (IImportDecl _ m) = text "import" <+> ppMIdent m

> ppIDecl :: IDecl -> Doc
> ppIDecl (IInfixDecl _ fix p op) = ppPrec fix p <+> ppQInfixOp op
> ppIDecl (HidingDataDecl _ tc tvs) =
>   text "hiding" <+> ppITypeDeclLhs "data" tc tvs
> ppIDecl (IDataDecl _ tc tvs cs) =
>   sep (ppITypeDeclLhs "data" tc tvs :
>        map indent (zipWith (<+>) (equals : repeat vbar) (map ppIConstr cs)))
>   where ppIConstr = maybe (char '_') ppConstr
> ppIDecl (INewtypeDecl _ tc tvs nc) =
>   sep [ppITypeDeclLhs "newtype" tc tvs <+> equals,indent (ppNewConstr nc)]
> ppIDecl (ITypeDecl _ tc tvs ty) =
>   sep [ppITypeDeclLhs "type" tc tvs <+> equals,indent (ppTypeExpr 0 ty)]
> ppIDecl (HidingClassDecl _ cls tv) =
>   text "hiding" <+> ppIClassDecl (ppITypeDeclLhs "class" cls [tv]) []
> ppIDecl (IClassDecl _ cls tv ds) =
>   ppIClassDecl (ppITypeDeclLhs "class" cls [tv]) ds
> ppIDecl (IInstanceDecl _ cls ty) =
>   text "instance" <+> ppQIdent cls <+> ppTypeExpr 2 ty
> ppIDecl (IFunctionDecl _ f ty) =
>   ppQIdent f <+> text "::" <+> ppQualTypeExpr ty

> ppITypeDeclLhs :: String -> QualIdent -> [Ident] -> Doc
> ppITypeDeclLhs kw tc tvs = text kw <+> ppQIdent tc <+> hsep (map ppIdent tvs)

> ppIClassDecl :: Doc -> [Maybe IMethodDecl] -> Doc
> ppIClassDecl head ds
>   | null ds = head
>   | otherwise = ppIBlock head (map (maybe (text "_") ppIMethodDecl) ds)

> ppIMethodDecl :: IMethodDecl -> Doc
> ppIMethodDecl (IMethodDecl p f ty) =
>   ppIDecl (IFunctionDecl p (qualify f) (QualTypeExpr [] ty))

> ppIBlock :: Doc -> [Doc] -> Doc
> ppIBlock prefix ds =
>   prefix <+> text "where" <+> lbrace $$
>   vcat (punctuate semi ds) $$
>   rbrace

\end{verbatim}
Types
\begin{verbatim}

> ppQualTypeExpr :: QualTypeExpr -> Doc
> ppQualTypeExpr (QualTypeExpr cx ty) = sep [ppContext cx,ppTypeExpr 0 ty]

> ppContext :: [ClassAssert] -> Doc
> ppContext [] = empty
> ppContext [ca] = ppClassAssert ca <+> text "=>"
> ppContext cas = parenList (map ppClassAssert cas) <+> text "=>"

> ppClassAssert :: ClassAssert -> Doc
> ppClassAssert (ClassAssert cls tv) = ppQIdent cls <+> ppIdent tv

> ppTypeExpr :: Int -> TypeExpr -> Doc
> ppTypeExpr p (ConstructorType tc tys) =
>   parenExp (p > 1 && not (null tys))
>            (ppQIdent tc <+> fsep (map (ppTypeExpr 2) tys))
> ppTypeExpr _ (VariableType tv) = ppIdent tv
> ppTypeExpr _ (TupleType tys) = parenList (map (ppTypeExpr 0) tys)
> ppTypeExpr _ (ListType ty) = brackets (ppTypeExpr 0 ty)
> ppTypeExpr p (ArrowType ty1 ty2) =
>   parenExp (p > 0) (fsep (ppArrowType (ArrowType ty1 ty2)))
>   where ppArrowType (ArrowType ty1 ty2) =
>           ppTypeExpr 1 ty1 <+> rarrow : ppArrowType ty2
>         ppArrowType ty = [ppTypeExpr 0 ty]

\end{verbatim}
Literals
\begin{verbatim}

> ppLiteral :: Literal -> Doc
> ppLiteral (Char c) = text (show c)
> ppLiteral (Int i) = int i
> ppLiteral (Float f)
>   | f < 0.0 = ppInfixOp fminusId <> double (-f)
>   | otherwise = double f
> ppLiteral (String s) = text (show s)

\end{verbatim}
Patterns
\begin{verbatim}

> ppConstrTerm :: Int -> ConstrTerm a -> Doc
> ppConstrTerm p (LiteralPattern _ l) =
>   parenExp (p > 1 && isNegative l) (ppLiteral l)
>   where isNegative (Char _) = False
>         isNegative (Int i) = i < 0
>         isNegative (Float f) = f < 0.0
>         isNegative (String _ ) = False
> ppConstrTerm p (NegativePattern _ l) =
>   parenExp (p > 1) (ppInfixOp (negOp l) <> ppLiteral l)
>   where negOp (Int _) = minusId
>         negOp (Float _) = fminusId
>         negOp _ = error "internal error: ppConstrTerm (NegativePattern)"
> ppConstrTerm _ (VariablePattern _ v) = ppIdent v
> ppConstrTerm p (ConstructorPattern _ c ts) =
>   parenExp (p > 1 && not (null ts))
>            (ppQIdent c <+> fsep (map (ppConstrTerm 2) ts))
> ppConstrTerm p (InfixPattern _ t1 c t2) =
>   parenExp (p > 0)
>            (sep [ppConstrTerm 1 t1 <+> ppQInfixOp c,
>                  indent (ppConstrTerm 0 t2)])
> ppConstrTerm _ (ParenPattern t) = parens (ppConstrTerm 0 t)
> ppConstrTerm _ (TuplePattern ts) = parenList (map (ppConstrTerm 0) ts)
> ppConstrTerm _ (ListPattern _ ts) = bracketList (map (ppConstrTerm 0) ts)
> ppConstrTerm _ (AsPattern v t) = ppIdent v <> char '@' <> ppConstrTerm 2 t
> ppConstrTerm _ (LazyPattern t) = char '~' <> ppConstrTerm 2 t

\end{verbatim}
Expressions
\begin{verbatim}

> ppCondExpr :: Doc -> CondExpr a -> Doc
> ppCondExpr eq (CondExpr _ g e) =
>   vbar <+> sep [ppExpr 0 g <+> eq,indent (ppExpr 0 e)]

> ppExpr :: Int -> Expression a -> Doc
> ppExpr _ (Literal _ l) = ppLiteral l
> ppExpr _ (Variable _ v) = ppQIdent v
> ppExpr _ (Constructor _ c) = ppQIdent c
> ppExpr _ (Paren e) = parens (ppExpr 0 e)
> ppExpr p (Typed e ty) =
>   parenExp (p > 0) (ppExpr 0 e <+> text "::" <+> ppQualTypeExpr ty)
> ppExpr _ (Tuple es) = parenList (map (ppExpr 0) es)
> ppExpr _ (List _ es) = bracketList (map (ppExpr 0) es)
> ppExpr _ (ListCompr e qs) =
>   brackets (ppExpr 0 e <+> vbar <+> list (map ppStmt qs))
> ppExpr _ (EnumFrom e) = brackets (ppExpr 0 e <+> text "..")
> ppExpr _ (EnumFromThen e1 e2) =
>   brackets (ppExpr 0 e1 <> comma <+> ppExpr 0 e2 <+> text "..")
> ppExpr _ (EnumFromTo e1 e2) =
>   brackets (ppExpr 0 e1 <+> text ".." <+> ppExpr 0 e2)
> ppExpr _ (EnumFromThenTo e1 e2 e3) =
>   brackets (ppExpr 0 e1 <> comma <+> ppExpr 0 e2
>               <+> text ".." <+> ppExpr 0 e3)
> ppExpr p (UnaryMinus op e) = parenExp (p > 1) (ppInfixOp op <> ppExpr 1 e)
> ppExpr p (Apply e1 e2) =
>   parenExp (p > 1) (sep [ppExpr 1 e1,indent (ppExpr 2 e2)])
> ppExpr p (InfixApply e1 op e2) =
>   parenExp (p > 0) (sep [ppExpr 1 e1 <+> ppQInfixOp (opName op),
>                          indent (ppExpr 1 e2)])
> ppExpr _ (LeftSection e op) = parens (ppExpr 1 e <+> ppQInfixOp (opName op))
> ppExpr _ (RightSection op e) = parens (ppQInfixOp (opName op) <+> ppExpr 1 e)
> ppExpr p (Lambda t e) =
>   parenExp (p > 0)
>            (sep [backsl <> fsep (map (ppConstrTerm 2) t) <+> rarrow,
>                  indent (ppExpr 0 e)])
> ppExpr p (Let ds e) =
>   parenExp (p > 0)
>            (sep [text "let" <+> ppBlock ds <+> text "in",ppExpr 0 e])
> ppExpr p (Do sts e) =
>   parenExp (p > 0) (text "do" <+> (vcat (map ppStmt sts) $$ ppExpr 0 e))
> ppExpr p (IfThenElse e1 e2 e3) =
>   parenExp (p > 0)
>            (text "if" <+>
>             sep [ppExpr 0 e1,
>                  text "then" <+> ppExpr 0 e2,
>                  text "else" <+> ppExpr 0 e3])
> ppExpr p (Case e alts) =
>   parenExp (p > 0)
>            (text "case" <+> ppExpr 0 e <+> text "of" $$
>             indent (vcat (map ppAlt alts)))

> ppStmt :: Statement a -> Doc
> ppStmt (StmtExpr e) = ppExpr 0 e
> ppStmt (StmtBind t e) = sep [ppConstrTerm 0 t <+> larrow,indent (ppExpr 0 e)]
> ppStmt (StmtDecl ds) = text "let" <+> ppBlock ds

> ppAlt :: Alt a -> Doc
> ppAlt (Alt _ t rhs) = ppRule (ppConstrTerm 0 t) rarrow rhs

> ppOp :: InfixOp a -> Doc
> ppOp (InfixOp _ op) = ppQInfixOp op
> ppOp (InfixConstr _ op) = ppQInfixOp op

\end{verbatim}
Goals
\begin{verbatim}

> ppGoal :: Goal a -> Doc
> ppGoal (Goal _ e ds) = sep [ppExpr 0 e,indent (ppLocalDefs ds)]

\end{verbatim}
Names
\begin{verbatim}

> ppIdent :: Ident -> Doc
> ppIdent x = parenExp (isInfixOp x) (text (name x))

> ppQIdent :: QualIdent -> Doc
> ppQIdent x = parenExp (isQInfixOp x) (text (qualName x))

> ppInfixOp :: Ident -> Doc
> ppInfixOp x = backQuoteExp (not (isInfixOp x)) (text (name x))

> ppQInfixOp :: QualIdent -> Doc
> ppQInfixOp x = backQuoteExp (not (isQInfixOp x)) (text (qualName x))

> ppMIdent :: ModuleIdent -> Doc
> ppMIdent m = text (moduleName m)

> ppIdentList :: [Ident] -> Doc
> ppIdentList = list . map ppIdent

\end{verbatim}
Print printing utilities
\begin{verbatim}

> indent :: Doc -> Doc
> indent = nest 2

> maybePP :: (a -> Doc) -> Maybe a -> Doc
> maybePP pp = maybe empty pp

> parenExp :: Bool -> Doc -> Doc
> parenExp b doc = if b then parens doc else doc

> backQuoteExp :: Bool -> Doc -> Doc
> backQuoteExp b doc = if b then backQuote <> doc <> backQuote else doc

> list, parenList, bracketList, braceList :: [Doc] -> Doc
> list = fsep . punctuate comma
> parenList = parens . list
> bracketList = brackets . list
> braceList = braces . list

> backQuote,backsl,vbar,rarrow,larrow :: Doc
> backQuote = char '`'
> backsl = char '\\'
> vbar = char '|'
> rarrow = text "->"
> larrow = text "<-"

\end{verbatim}
