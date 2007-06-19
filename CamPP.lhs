% -*- LaTeX -*-
% $Id: CamPP.lhs 2290 2007-06-19 21:48:25Z wlux $
%
% Copyright (c) 2002-2007, Wolfgang Lux
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
>   ppKW "data" <+> ppName tc <> (if null vs then empty else ppNames vs)
>               <+> sep (zipWith (<+>) (equals : repeat bar) (map ppConstr cs))
> ppDecl (FunctionDecl f vs st) =
>   ppCode (ppKW "function" <+> ppName f <> ppNames vs) st

> ppConstr :: ConstrDecl -> Doc
> ppConstr (ConstrDecl c tys) =
>   ppName c <> if null tys then empty else ppList ppType tys

> ppType :: Type -> Doc
> ppType (TypeVar v) = ppName v
> ppType (TypeApp tc tys) = ppName tc <> ppList ppType tys
> ppType (TypeArr ty1 ty2) = ppType ty1 <+> text "->" <+> ppType ty2

> ppCode :: Doc -> Stmt -> Doc
> ppCode prefix = ppBlock prefix . ppStmt

> ppBlock :: Doc -> Doc -> Doc
> ppBlock prefix x = sep [prefix <+> lbrace,nest blockIndent x,rbrace]

> ppStmt :: Stmt -> Doc
> ppStmt (Return e) = ppKW "return" <+> ppExpr e
> ppStmt (Enter v) = ppKW "enter" <+> ppName v
> ppStmt (Exec f vs) = ppKW "exec" <+> ppName f <> ppNames vs
> ppStmt (CCall h ty cc) =
>   ppKW "ccall" <+> maybe empty ppHeader h <+> ppCRetType ty <> ppCCall cc
>   where ppHeader h = char '"' <> text h <> char '"'
> ppStmt (Seq st1 st2) = ppStmt0 st1 <> semi $$ ppStmt st2
> ppStmt (Switch rf v cases) =
>   ppBlock (ppKW "switch" <+> ppName v <+> ppRF rf) (ppAlts ppCase cases)
>   where ppRF Rigid = ppKW "rigid"
>         ppRF Flex = ppKW "flex"
> ppStmt (Choices alts) = ppBlock (ppKW "choices") (ppAlts ppAlt alts)

> ppStmt0 :: Stmt0 -> Doc
> ppStmt0 (Lock v) = ppKW "lock" <+> ppName v
> ppStmt0 (Update v1 v2) = ppKW "update" <+> ppName v1 <+> ppName v2
> ppStmt0 (v :<- st) =
>   case st of
>     Seq _ _ -> ppBlock prefix (ppStmt st)
>     _       -> prefix <+> ppStmt st
>   where prefix = ppName v <+> text "<-"
> ppStmt0 (Let bds) = ppKW "let" <+> ppBindings (map ppBinding bds)
>   where ppBinding (Bind v n) = ppName v <+> equals <+> ppExpr n

> ppBindings :: [Doc] -> Doc
> ppBindings bds = lbrace <+> vcat (punctuate semi bds) <+> rbrace

> ppLiteral :: Literal -> Doc
> ppLiteral (Char c) = ppKW "char" <+> int (ord c)
> ppLiteral (Int i) = ppKW "int" <+> int i
> ppLiteral (Float f) = ppKW "float" <+> double f

> ppExpr :: Expr -> Doc
> ppExpr (Lit c) = ppLiteral c
> ppExpr (Constr c vs) = ppKW "data" <+> ppName c <> ppNames vs
> ppExpr (Papp f vs) = ppKW "papp" <+> ppName f <> ppNames vs
> ppExpr (Closure f vs) = ppKW "function" <+> ppName f <> ppNames vs
> ppExpr (Lazy f vs) = ppKW "lazy" <+> ppName f <> ppNames vs
> ppExpr Free = ppKW "free"
> ppExpr (Var v) = ppName v

> ppAlts :: (a -> Doc) -> [a] -> Doc
> ppAlts ppAlt = vcat . zipWith (<+>) (space : repeat bar) . map ppAlt

> ppCase :: Case -> Doc
> ppCase (Case t st) = ppCode (ppTag t <> colon) st
>   where ppTag (LitCase c) = ppLiteral c
>         ppTag (ConstrCase c vs) = ppKW "data" <+> ppName c <> ppNames vs
>         ppTag DefaultCase = ppKW "default"

> ppAlt :: Stmt -> Doc
> ppAlt = ppCode empty

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
> ppCArgType TypeFunPtr = parens (ppKW "function")
> ppCArgType TypeStablePtr = parens (ppKW "stable")
> ppCArgType TypeNodePtr = text ""          -- Do not replace text "" by empty!

> ppCRetType :: CRetType -> Doc
> ppCRetType = maybe (parens (ppKW "unit")) ppCArgType

> ppKW :: String -> Doc
> ppKW kw = char '.' <> text kw

> ppName :: Name -> Doc
> ppName = text . show

> ppNames :: [Name] -> Doc
> ppNames = ppList ppName

> ppList :: (a -> Doc) -> [a] -> Doc
> ppList f = parens . fsep . punctuate comma . map f

> bar :: Doc
> bar = char '|'

\end{verbatim}
