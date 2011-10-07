% -*- LaTeX -*-
% $Id: ILPP.lhs 3056 2011-10-07 16:27:03Z wlux $
%
% Copyright (c) 1999-2011 Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{ILPP.lhs}
\section{A Pretty Printer for the Intermediate Language}
This module implements just another pretty printer, this time for the
intermediate language. It was mainly adapted from the Curry pretty
printer (see Sect.~\ref{sec:CurryPP}) which, in turn, is based on Simon
Marlow's pretty printer for Haskell.
\begin{verbatim}

> module ILPP(module ILPP, Doc) where
> import IL
> import PredefIdent
> import Pretty

> default(Int,Double)

> dataIndent = 2
> bodyIndent = 2
> exprIndent = 2
> caseIndent = 2
> altIndent = 2

> ppModule :: Module -> Doc
> ppModule (Module m es is ds) =
>   vcat (ppHeader m es : map ppImport is ++ map ppDecl ds)

> ppHeader :: ModuleIdent -> [QualIdent] -> Doc
> ppHeader m es =
>   text "module" <+> text (show m) <+> ppTuple ppQIdent es <+> text "where"

> ppImport :: ModuleIdent -> Doc
> ppImport m = text "import" <+> text (show m)

> ppDecl :: Decl -> Doc
> ppDecl (DataDecl tc n cs) =
>   sep (text "data" <+> ppTypeLhs tc n :
>        map (nest dataIndent)
>            (zipWith (<+>) (equals : repeat (char '|')) (map ppConstr cs)))
> ppDecl (TypeDecl tc n ty) =
>   sep [text "type" <+> ppTypeLhs tc n <+> equals,
>        nest dataIndent (ppType 2 ty)]
> ppDecl (FunctionDecl f vs ty exp) =
>   ppTypeSig f ty $$
>   sep [ppQIdent f <+> hsep (map ppIdent vs) <+> equals,
>        nest bodyIndent (ppExpr 0 exp)]
> ppDecl (ForeignDecl f cc ie ty) =
>   sep [text "foreign import" <+> ppCallConv cc <+> text (show ie),
>        nest bodyIndent (ppTypeSig f ty)]
>   where ppCallConv Primitive = text "primitive"
>         ppCallConv CCall = text "ccall"
>         ppCallConv RawCall = text "rawcall"

> ppTypeLhs :: QualIdent -> Int -> Doc
> ppTypeLhs tc n = ppQIdent tc <+> hsep (map text (take n typeVars))

> ppConstr :: ConstrDecl -> Doc
> ppConstr (ConstrDecl c tys) = ppQIdent c <+> fsep (map (ppType 2) tys)

> ppTypeSig :: QualIdent -> Type -> Doc
> ppTypeSig f ty = ppQIdent f <+> text "::" <+> ppType 0 ty

> ppType :: Int -> Type -> Doc
> ppType p (TypeConstructor tc tys)
>   | isQTupleId tc && length tys == qTupleArity tc = ppTuple (ppType 0) tys
>   | tc == qListId && length tys == 1 = brackets (ppType 0 (head tys))
>   | otherwise =
>       ppParen (p > 1 && not (null tys))
>               (ppQIdent tc <+> fsep (map (ppType 2) tys))
> ppType _ (TypeVariable n)
>   | n >= 0 = text (typeVars !! n)
>   | otherwise = text ('_':show (-n))
> ppType p (TypeArrow ty1 ty2) =
>   ppParen (p > 0) (fsep (ppArrow (TypeArrow ty1 ty2)))
>   where ppArrow (TypeArrow ty1 ty2) =
>           ppType 1 ty1 <+> text "->" : ppArrow ty2
>         ppArrow ty = [ppType 0 ty]

> ppBinding :: Binding -> Doc
> ppBinding (Binding v exp) =
>   sep [ppIdent v <+> equals,nest bodyIndent (ppExpr 0 exp)]

> ppAlt :: Alt -> Doc
> ppAlt (Alt pat exp) =
>   sep [ppConstrTerm pat <+> text "->",nest altIndent (ppExpr 0 exp)]

> ppLiteral :: Literal -> Doc
> ppLiteral (Char c) = text (show c)
> ppLiteral (Int i) = integer i
> ppLiteral (Integer i) = integer i
> ppLiteral (Float f) = double f

> ppConstrTerm :: ConstrTerm -> Doc
> ppConstrTerm (LiteralPattern l) = ppLiteral l
> ppConstrTerm (ConstructorPattern c [v1,v2])
>   | isQInfixOp c = ppIdent v1 <+> ppQInfixOp c <+> ppIdent v2
> ppConstrTerm (ConstructorPattern c vs)
>   | isQTupleId c = ppTuple ppIdent vs
>   | otherwise = ppQIdent c <+> fsep (map ppIdent vs)
> ppConstrTerm (VariablePattern v) = ppIdent v

> ppExpr :: Int -> Expression -> Doc
> ppExpr p (Literal l) = ppLiteral l
> ppExpr p (Variable v) = ppIdent v
> ppExpr p (Function f _) = ppQIdent f
> ppExpr p (Constructor c _) = ppQIdent c
> ppExpr p (Apply e1 e2) =
>   case e1 of
>     Apply (Function f _) e | isQInfixOp f -> ppInfixApp p e f e2
>     Apply (Constructor c _) e | isQInfixOp c -> ppInfixApp p e c e2
>     _ -> ppParen (p > 2) (sep [ppExpr 2 e1,nest exprIndent (ppExpr 3 e2)])
> ppExpr p (Case ev e as) =
>   ppParen (p > 0)
>           (ppCase ev <+> ppExpr 0 e <+> text "of" $$
>            nest caseIndent (vcat (map ppAlt as)))
>   where ppCase Rigid = text "case"
>         ppCase Flex = text "fcase"
> ppExpr p (Choice es) =
>   ppParen (p > 0)
>           (sep (zipWith (<+>)
>                         (empty : repeat (char '|'))
>                         (map (ppExpr 1) es)))
> ppExpr p (Exist vs e) =
>   ppParen (p > 0)
>           (sep [text "let" <+> ppIdentList vs <+> text "free" <+> text "in",
>                 ppExpr 0 e])
>   where ppIdentList = fsep . punctuate comma . map ppIdent
> ppExpr p (Let rec bs e) =
>   ppParen (p > 0)
>           (sep [ppLet rec <+> vcat (map ppBinding bs) <+> text "in",
>                 ppExpr 0 e])
>   where ppLet NonRec = text "let"
>         ppLet Rec = text "letrec"
> ppExpr p (SrcLoc _ e) = ppExpr p e

> ppInfixApp :: Int -> Expression -> QualIdent -> Expression -> Doc
> ppInfixApp p e1 op e2 =
>   ppParen (p > 1)
>           (sep [ppExpr 2 e1 <+> ppQInfixOp op,nest exprIndent (ppExpr 2 e2)])

> ppIdent :: Ident -> Doc
> ppIdent ident
>   | isInfixOp ident = parens (ppName ident)
>   | otherwise = ppName ident

> ppQIdent :: QualIdent -> Doc
> ppQIdent ident
>   | isQInfixOp ident = parens (ppQual ident)
>   | otherwise = ppQual ident

> ppQInfixOp :: QualIdent -> Doc
> ppQInfixOp op
>   | isQInfixOp op = ppQual op
>   | otherwise = char '`' <> ppQual op <> char '`'

> ppName :: Ident -> Doc
> ppName x = text (name x)

> ppQual :: QualIdent -> Doc
> ppQual x = text (qualName x)

> typeVars :: [String]
> typeVars = [mkTypeVar c i | i <- [0..], c <- ['a' .. 'z']]
>   where mkTypeVar c i = c : if i == 0 then [] else show i

> ppParen :: Bool -> Doc -> Doc
> ppParen p = if p then parens else id

> ppTuple :: (a -> Doc) -> [a] -> Doc
> ppTuple f = parens . fsep . punctuate comma . map f

\end{verbatim}
