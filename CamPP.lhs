% -*- LaTeX -*-
% $Id: CamPP.lhs 3152 2014-02-12 18:08:19Z wlux $
%
% Copyright (c) 2002-2013, Wolfgang Lux
% See LICENSE for the full license.
%
\subsection{Pretty-printing Abstract Machine Code}
\begin{verbatim}

> module CamPP where
> import Cam
> import Char
> import Pretty

> default(Int)

> blockIndent = 2

> ppModule :: Module -> Doc
> ppModule ds = vcat $ punctuate semi $ map ppDecl ds

> ppDecl :: Decl -> Doc
> ppDecl (ImportDecl m) = ppKW "import" <+> ppName m
> ppDecl (DataDecl tc vs cs) =
>   sep (ppKW "data" <+> ppName tc <> (if null vs then empty else ppNames vs) :
>        zipWith ppConstrDecl (equals : repeat bar) cs)
>   where ppConstrDecl sep c = nest blockIndent (sep <+> ppConstr c)
> ppDecl (FunctionDecl vb f vs st) =
>   ppBlock (ppVis vb <+> ppName f <> ppNames vs) (ppStmt st)

> ppConstr :: ConstrDecl -> Doc
> ppConstr (ConstrDecl vb c tys) =
>   ppVis vb <+> ppName c <> if null tys then empty else ppList ppType tys

> ppType :: Type -> Doc
> ppType (TypeVar v) = ppName v
> ppType (TypeApp tc tys) = ppName tc <> ppList ppType tys
> ppType (TypeArr ty1 ty2) = ppType ty1 <+> text "->" <+> ppType ty2

> ppBlock :: Doc -> Doc -> Doc
> ppBlock prefix x = sep [prefix <+> lbrace,nest blockIndent x,rbrace]

> ppStmt :: Stmt -> Doc
> ppStmt (Return e) = ppKW "return" <+> ppExpr e
> ppStmt (Eval v) = ppKW "eval" <+> ppName v
> ppStmt (Exec f vs) = ppName f <> ppNames vs
> ppStmt (Apply v vs) = ppKW "apply" <+> ppName v <+> ppNames vs
> ppStmt (CCall h ty cc) =
>   ppKW "ccall" <+> maybe empty ppHeader h <+> ppCRetType ty <> ppCCall cc
>   where ppHeader h = char '"' <> text h <> char '"'
> ppStmt (Seq st1 st2) = ppStmt0 st1 <> semi $$ ppStmt st2
> ppStmt (Let ds st) =
>   sep [ppKW "let" <+> ppBindings ds <+> ppKW "in",ppStmt st]
> ppStmt (Switch rf v cases) =
>   ppAlts (ppKW "switch" <+> ppName v <+> ppRF rf) ppCase cases
>   where ppRF Rigid = ppKW "rigid"
>         ppRF Flex = ppKW "flex"
> ppStmt (Choice alts) = ppAlts (ppKW "choice") ppStmt alts

> ppStmt0 :: Stmt0 -> Doc
> ppStmt0 (v :<- st) =
>   case st of
>     Seq _ _ -> ppBlock prefix (ppStmt st)
>     Let _ _ -> ppBlock prefix (ppStmt st)
>     _       -> sep [prefix,nest blockIndent (ppStmt st)]
>   where prefix = ppName v <+> text "<-"

> ppBindings :: [Bind] -> Doc
> ppBindings ds = lbrace <+> vcat (punctuate semi (map ppBinding ds)) <+> rbrace

> ppBinding :: Bind -> Doc
> ppBinding (Bind v n) = sep [ppName v <+> equals,nest blockIndent (ppExpr n)]

> ppLiteral :: Literal -> Doc
> ppLiteral (Char c) = ppKW "char" <+> int (ord c)
> ppLiteral (Int i) = ppKW "int" <+> integer i
> ppLiteral (Integer i) = ppKW "integer" <+> integer i
> ppLiteral (Float f) = ppKW "float" <+> double f

> ppExpr :: Expr -> Doc
> ppExpr (Lit c) = ppLiteral c
> ppExpr (Constr c vs) = ppKW "data" <+> ppName c <> ppNames vs
> ppExpr (Papp f vs) = ppKW "papp" <+> ppName f <> ppNames vs
> ppExpr (Closure f vs) = ppKW "fun" <+> ppName f <> ppNames vs
> ppExpr (Lazy f vs) = ppKW "lazy" <+> ppName f <> ppNames vs
> ppExpr Free = ppKW "free"
> ppExpr (Var v) = ppName v

> ppAlts :: Doc -> (a -> Doc) -> [a] -> Doc
> ppAlts prefix ppAlt as =
>   sep [prefix <+> lbrace,
>        vcat (zipWith ($) (nest 2 : repeat ((<+>) bar)) (map ppAlt as)),
>        rbrace]

> ppCase :: Case -> Doc
> ppCase (Case t st) = sep [ppTag t <> colon,nest blockIndent (ppStmt st)]
>   where ppTag (LitCase c) = ppLiteral c
>         ppTag (ConstrCase c vs) = ppKW "data" <+> ppName c <> ppNames vs
>         ppTag DefaultCase = ppKW "default"

> ppCCall :: CCall -> Doc
> ppCCall (StaticCall f xs) = ppCFunCall (text f) xs
> ppCCall (DynamicCall v xs) = ppCFunCall (parens (char '*' <> ppName v)) xs
> ppCCall (StaticAddr x) = char '&' <> text x

> ppCFunCall :: Doc -> [(CArgType,Name)] -> Doc
> ppCFunCall f xs = f <> ppList arg xs
>   where arg (ty,v) = ppCArgType ty <> ppName v

> ppCArgType :: CArgType -> Doc
> ppCArgType TypeBool = parens (ppKW "bool")
> ppCArgType TypeChar = parens (ppKW "char")
> ppCArgType TypeInt = parens (ppKW "int")
> ppCArgType TypeFloat = parens (ppKW "float")
> ppCArgType TypePtr = parens (ppKW "pointer")
> ppCArgType TypeFunPtr = parens (ppKW "fun")
> ppCArgType TypeStablePtr = parens (ppKW "stable")
> ppCArgType TypeNodePtr = text ""          -- Do not replace text "" by empty!

> ppCRetType :: CRetType -> Doc
> ppCRetType = maybe (parens (ppKW "unit")) ppCArgType

> ppKW :: String -> Doc
> ppKW kw = char '.' <> text kw

> ppVis :: Visibility -> Doc
> ppVis Private = ppKW "private"
> ppVis Exported = empty

> ppName :: Name -> Doc
> ppName = text . show

> ppNames :: [Name] -> Doc
> ppNames = ppList ppName

> ppList :: (a -> Doc) -> [a] -> Doc
> ppList f = parens . fsep . punctuate comma . map f

> bar :: Doc
> bar = char '|'

\end{verbatim}
