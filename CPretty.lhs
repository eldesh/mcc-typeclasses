% -*- LaTeX -*-
% $Id: CPretty.lhs 2453 2007-08-23 22:58:14Z wlux $
%
% Copyright (c) 2002-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CPretty.lhs}
\subsection{Pretty-Printing}
The module \texttt{CPretty} implements a pretty printer for the
abstract C syntax tree. Actually, the generated code is not really
pretty, as this module has been tuned towards efficienct code
generation. If you want prettier code, run the code through a C
program formatter.\footnote{For instance, on Unix systems
\texttt{indent(1)} can be used for that purpose.}
\begin{verbatim}

> module CPretty where

> import CCode
> import Pretty
> import List

> ppCFile :: CFile -> Doc
> ppCFile = vsep . map ppTopDecl

> ppTopDecl :: CTopDecl -> Doc
> ppTopDecl (CppInclude f) = text "#include" <+> char '<' <> text f <> char '>'
> ppTopDecl (CppCondDecls c ds1 ds2)
>   | null (ds1 ++ ds2) = empty
>   | otherwise =
>       text "#if" <+> ppExpr 0 c $+$
>       vsep (map ppTopDecl ds1) $+$
>       ppElse ds2 $+$
>       text "#endif"
>  where ppElse ds
>          | null ds = empty
>          | otherwise = text "#else" $+$ vsep (map ppTopDecl ds)
> ppTopDecl (CppDefine v e) = text "#define" <+> text v <+> ppExpr 0 e
> ppTopDecl (CExternVarDecl ty v) =
>   ppLinkage True CPublic <+> varDecl ty v <> semi
> ppTopDecl (CExternArrayDecl ty v) =
>   ppLinkage True CPublic <+> arrayDecl ty v <> semi
> ppTopDecl (CEnumDecl cs)
>   | null cs = empty
>   | otherwise = text "enum" $+$ block (list ppConst cs) <> semi
> ppTopDecl (CFuncDecl vb f) =
>   ppFunCall "DECLARE_LABEL" [ppLinkage True vb,text f] <> semi
> ppTopDecl (CVarDef vb ty v (CInit x)) =
>   ppLinkage False vb <+> varDecl ty v <> equals <> ppExpr 0 x <> semi
> ppTopDecl (CVarDef vb ty v (CStruct xs)) =
>   ppLinkage False vb <+> varDecl ty v <> equals $+$ ppInits xs <> semi
> ppTopDecl (CArrayDef vb ty v xs) =
>   ppLinkage False vb <+> arrayDecl ty v <> equals $+$ ppInits xs <> semi
> ppTopDecl (CFuncDef vb f sts) =
>   ppLinkage False vb <+> ppFunCall "FUNCTION" [text f] $+$
>   ppBlock (ppFunCall "ENTRY_LABEL" [ppLinkage True vb,text f]) sts
> ppTopDecl (CMainDecl f xs) =
>   ppLinkage True CPublic <+> ppHeader (text f) xs <> semi
>   where ppHeader f xs =
>           ppDeclarator 0 (CFunctionType retType (zipWith const argTypes xs)) f
>           where CFunctionType retType argTypes = cMainType
> ppTopDecl (CMainFunc f xs sts) =
>   ppLinkage False CPublic <+> ppHeader f xs $+$ ppBlock empty sts
>   where ppHeader f xs =
>           ppDeclarator 0 retType (ppFunCall f (zipWith varDecl argTypes xs))
>           where CFunctionType retType argTypes = cMainType

> cMainType :: CType
> cMainType = CFunctionType intType [intType,pStrType,pStrType]
>   where intType = CType "int"
>         pStrType = CPointerType (CPointerType (CType "char"))

> ppLinkage :: Bool -> CVisibility -> Doc
> ppLinkage decl CPublic = if decl then text "extern" else empty
> ppLinkage _ CPrivate = text "static"

> ppConst :: CConst -> Doc
> ppConst (CConst c x) = text c <> maybe empty (\i -> equals <> integer i) x

> ppInits :: [CInitializer] -> Doc
> ppInits xs = block (list ppInit xs)

> ppInit :: CInitializer -> Doc
> ppInit (CInit x) = ppExpr 0 x
> ppInit (CStruct xs) = braces $ hcat $ list ppInit xs

\end{verbatim}
When a code block is printed, the compiler filters out its local
declarations and emits them at the beginning of the block. The
function \texttt{ppBlock} can insert an arbitrary code sequence
between the declarations and the statements. This allows inserting the
entry label into a function block. For nested blocks no additional
code is inserted. As all code before the entry point is skipped when
using the direct jump model, \texttt{ppBlock} replaces the
declarations by assignments to the declared variables at the places
where they occur in the block.

Multiple declarations for the same local variable are permitted and 
merged into a single declaration. Thus, the C code generator can use 
generic names like \texttt{retIp} in the code without having to check 
whether a declaration for the variable is present in the code already.
\begin{verbatim}

> ppBlock :: Doc -> CBlock -> Doc
> ppBlock entry sts = block (map ppDecl ds ++ entry : map ppStmt sts)
>   where ds = nubBy sameVar (foldr collectDecl [] sts)
>         sameVar (CLocalVar ty1 v1 _) (CLocalVar ty2 v2 _) =
>           ty1 == ty2 && v1 == v2
>         sameVar _ _ = False

> ppNestedBlock :: CBlock -> Doc
> ppNestedBlock = ppBlock empty

> collectDecl :: CStmt -> [CStmt] -> [CStmt]
> collectDecl (CLocalVar ty v _) ds = CLocalVar ty v Nothing : ds
> collectDecl (CStaticArray ty v xs) ds = CStaticArray ty v xs : ds
> collectDecl (CppCondStmts _ sts1 sts2) ds =
>   foldr collectDecl ds (sts1 ++ sts2)
> collectDecl _ ds = ds

> ppDecl :: CStmt -> Doc
> ppDecl (CLocalVar ty v _) = varDecl ty v <> semi
> ppDecl (CStaticArray ty v xs) = ppTopDecl (CArrayDef CPrivate ty v xs)

\end{verbatim}
The pretty printer ensures that every statement starts on a new line.
This is necessary in order to emit C-preprocessor directives without
checking for the current indentation.
\begin{verbatim}

> ppStmts :: [CStmt] -> Doc
> ppStmts = vsep . map ppStmt

> ppStmt :: CStmt -> Doc
> ppStmt (CLocalVar _ v x) = maybe empty (ppStmt . CAssign (LVar v)) x
> ppStmt (CStaticArray _ _ _) = empty
> ppStmt (CppCondStmts c sts1 sts2) =
>   text "#if" <+> text c $+$ ppStmts sts1 $+$ ppElse sts2 $+$ text "#endif"
>   where ppElse sts = if null sts then empty else text "#else" $+$ ppStmts sts
> ppStmt (CBlock sts) = ppNestedBlock sts
> ppStmt (CAssign x y) = ppLhs x <> equals <> ppExpr 0 y <> semi
> ppStmt (CIncrBy x y) = ppLhs x <> text "+=" <> ppExpr 0 y <> semi
> ppStmt (CDecrBy x y) = ppLhs x <> text "-=" <> ppExpr 0 y <> semi
> ppStmt (CProcCall f xs) = ppFunCall f (map (ppExpr 0) xs) <> semi
> ppStmt (CIf c sts1 sts2) =
>   text "if" <> parens (ppExpr 0 c) $+$ ppNestedBlock sts1 $+$ ppElse sts2
>   where ppElse sts =
>           case sts of
>             [] -> empty
>             [CIf c sts1 sts2] ->
>               text "else if" <> parens (ppExpr 0 c) $+$
>               ppNestedBlock sts1 $+$
>               ppElse sts2
>             _ -> text "else" $+$ ppNestedBlock sts
> ppStmt (CSwitch e cases) =
>   text "switch" <> parens (ppExpr 0 e) $+$ block (map ppCase cases)
> ppStmt (CLoop sts) = text "for(;;)" $+$ ppNestedBlock sts
> ppStmt CBreak = text "break" <> semi
> ppStmt CContinue = text "continue" <> semi
> ppStmt (CReturn e) = text "return" <+> ppExpr 0 e <> semi
> ppStmt (CLabel l) = text l <> colon
> ppStmt (CGoto l) = text "goto" <+> text l <> semi

> ppLhs :: LVar -> Doc
> ppLhs (LVar x) = text x
> ppLhs (LElem x i) = ppLhs x <> brackets (ppExpr 0 i)
> ppLhs (LField x f) = ppLhs x <> text "->" <> text f

\end{verbatim}
If the statement sequence following a case label contains any
declarations, the compiler automatically encloses the statements in a
nested block.
\begin{verbatim}

> ppCase :: CCase -> Doc
> ppCase (CCase l sts) = ppCaseLabel l <> colon $+$ ppCaseStmts sts

> ppCaseLabel :: CCaseLabel -> Doc
> ppCaseLabel (CCaseLabel c) = text "case" <+> text c
> ppCaseLabel (CCaseInt i) = text "case" <+> integer i
> ppCaseLabel CCaseDefault = text "default"

> ppCaseStmts :: [CStmt] -> Doc
> ppCaseStmts sts = if null ds then ppStmts sts else ppStmt (CBlock sts)
>   where ds = foldr collectDecl [] sts

\end{verbatim}
The expression printer uses a precedence level in order to insert
parentheses around subexpressions when this is necessary. This code
does not attempt to implement the full precedence hierarchy of ANSI C,
but uses a subset that is suitable for printing the expressions
generated by the compiler.

Note that a negative integer literal $l$ is replaced by an expression
$l'-1$, where $l'=l+1$. This is a portable solution to avoid a C
compiler warning ``decimal constant is so large that it is unsigned''
when emitting the largest possible negative integer ($-2^{31}$ on a
32-bit architecture and $-2^{63}$ on a 64-bit architecture).
\begin{verbatim}

> ppExpr :: Int -> CExpr -> Doc
> ppExpr _ CNull = text "0"
> ppExpr p (CInt i)
>   | i < 0 = ppParens (p > 3) $ integer (i + 1) <> text "-1"
>   | otherwise = integer i
> ppExpr _ (CFloat f) = double f
> ppExpr _ (CString s) = string s
> ppExpr _ (CElem x i) = ppExpr 6 x <> brackets (ppExpr 0 i)
> ppExpr _ (CField x f) = ppExpr 6 x <> text "->" <> text f
> ppExpr _ (CFunCall f xs) = ppFunCall f (map (ppExpr 0) xs)
> ppExpr p (CCond c t e) =
>   ppParens (p > 0) $ ppExpr 1 c <> text "?" <> ppExpr 0 t
>                                 <> text ":" <> ppExpr 0 e
> ppExpr p (CAdd x y) =
>   ppParens (p > 3) $ ppExpr 3 x <> text "+" <> ppExpr 3 y
> ppExpr p (CSub x y) =
>   ppParens (p > 3) $ ppExpr 3 x <> text "-" <> ppExpr 4 y
> ppExpr p (CMul x y) =
>   ppParens (p > 4) $ ppExpr 4 x <> text "*" <> ppExpr 4 y
> ppExpr p (CDiv x y) =
>   ppParens (p > 4) $ ppExpr 4 x <> text "/" <> ppExpr 5 y
> ppExpr p (CMod x y) =
>   ppParens (p > 4) $ ppExpr 4 x <> text "%" <> ppExpr 5 y
> ppExpr p (CShift x n)
>   | n > 0 = ppParens (p > 2) $ ppExpr 2 x <> text "<<" <> int n
>   | otherwise = ppParens (p > 2) $ ppExpr 2 x <> text ">>" <> int (-n)
> ppExpr p (CRel x rel y) =
>   ppParens (p > 1) $ ppExpr 2 x <> text rel <> ppExpr 2 y
> ppExpr p (CAddr x) = ppParens (p > 5) $ char '&' <> ppExpr 5 x
> ppExpr p (CCast ty x) = ppParens (p > 5) $ parens (ppType ty) <> ppExpr 5 x
> ppExpr _ (CExpr x) = text x

> ppType :: CType -> Doc
> ppType ty = ppDeclarator 0 ty empty

\end{verbatim}
Function types are always fully prototyped. In particular, the type of
a function with no arguments returning an \verb|int| is printed as
\verb|void (*)(void)|, not \verb|void (*)()|.
\begin{verbatim}

> ppDeclarator :: Int -> CType -> Doc -> Doc
> ppDeclarator _ (CType t) x = text t <+> x
> ppDeclarator _ (CConstType t) x = text "const" <+> text t <+> x
> ppDeclarator _ (CPointerType ty) x = ppDeclarator 1 ty (char '*' <> x)
> ppDeclarator _ (CConstPointerType ty) x =
>   ppDeclarator 1 ty (text "*const" <+> x)
> ppDeclarator p (CArrayType ty n) x =
>   ppDeclarator 0 ty (ppParens (p > 0) x <> brackets (maybe empty int n))
> ppDeclarator p (CFunctionType ty tys) x =
>   ppDeclarator 0 ty (ppParens (p > 0) x <> ppArgList ppType tys')
>   where tys' = if null tys then [voidType] else tys
>         voidType = CType "void"

> ppParens :: Bool -> Doc -> Doc
> ppParens b = if b then parens else id

> ppFunCall :: String -> [Doc] -> Doc
> ppFunCall f xs = text f <> ppArgList id xs

> ppArgList :: (a -> Doc) -> [a] -> Doc
> ppArgList f xs = parens (hcat (list f xs))

> block :: [Doc] -> Doc
> block xs = vsep (lbrace : xs ++ [rbrace])

> list :: (a -> Doc) -> [a] -> [Doc]
> list f xs = punctuate comma (map f xs)

> varDecl, arrayDecl :: CType -> String -> Doc
> varDecl ty v = ppDeclarator 0 ty (text v)
> arrayDecl ty v = varDecl (CArrayType ty Nothing) v

> string :: String -> Doc
> string = text . show

> vsep :: [Doc] -> Doc
> vsep = foldr ($+$) empty

\end{verbatim}
