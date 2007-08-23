% -*- LaTeX -*-
% $Id: CCode.lhs 2453 2007-08-23 22:58:14Z wlux $
%
% Copyright (c) 2002-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CCode.lhs}
\section{C Code}
The module \texttt{CCode} implements a simplified abstract syntax tree
for the C language. The module does not support the full C syntax, but
only the subset of the language needed by the Curry compiler. For
instance, it is not possible to define arbitrary C functions, but only
parameterless functions because the runtime system passes arguments to
a function on the (Curry) stack.
\begin{verbatim}

> module CCode where
> import List
> import Maybe
> infixl 9 `CElem`,`CField`
> infixr 8 `CCast`
> infixl 7 `CMul`,`CDiv`,`CMod`
> infixl 6 `CAdd`,`CSub`
> infixl 5 `CShift`

\end{verbatim}
\subsection{Abstract Syntax Tree}
A C file consists of a sequence of external declarations, variable
definitions, and function definitions. Conditional compilation is
possible with the help of \texttt{CppCondDecls}, which encloses its
declaration list with \verb|#if| and \verb|#endif| preprocessor
directives. The argument of \texttt{CppCondDecls} is used as condition
for the \verb|#if| directive.

The type specified in array declarations is that of the elements, not
the type of the array itself. This prevents illegal array
declarations, but also makes it impossible to define arrays which are
initialized only partially. Fortunately, we will not need such
initializations in the compiler.

No types need to be specified for the declaration of the \verb|main|
function because these types are fixed. However, the number of
arguments still matters and should agree between a \verb|CMainDecl|
declaration and its corresponding \verb|CMainFunc| definition.
\begin{verbatim}

> type CFile = [CTopDecl]

> data CTopDecl =
>     CppInclude String
>   | CppCondDecls CExpr [CTopDecl] [CTopDecl]
>   | CppDefine String CExpr
>   | CExternVarDecl CType String
>   | CExternArrayDecl CType String
>   | CEnumDecl [CConst]
>   | CFuncDecl CVisibility String
>   | CVarDef CVisibility CType String CInitializer
>   | CArrayDef CVisibility CType String [CInitializer]
>   | CFuncDef CVisibility String CBlock
>   | CMainDecl String [String]
>   | CMainFunc String [String] CBlock
>   deriving Eq

> data CVisibility = CPublic | CPrivate deriving Eq
> data CConst = CConst String (Maybe Integer) deriving Eq
> data CInitializer = CInit CExpr | CStruct [CInitializer] deriving Eq

\end{verbatim}
The body of a function consists of a list of statements and local
declarations. We are more liberal than C here in allowing declarations
and statements to be mixed.\footnote{Actually, this is allowed by the
ISO C99 standard, but not by ANSI C89.}

Similar to top-level declarations, conditional compilation inside a
function body is possible with the help of \texttt{CppCondStmts}. Note
that there are no \texttt{for} and \texttt{while} loops because they
are not used by the compiler.
\begin{verbatim}

> type CBlock = [CStmt]
> data CStmt =
>     CLocalVar CType String (Maybe CExpr)
>   | CStaticArray CType String [CInitializer]
>   | CppCondStmts String [CStmt] [CStmt]
>   | CBlock CBlock
>   | CAssign LVar CExpr
>   | CIncrBy LVar CExpr
>   | CDecrBy LVar CExpr
>   | CProcCall String [CExpr]
>   | CIf CExpr [CStmt] [CStmt]
>   | CSwitch CExpr [CCase]
>   | CLoop [CStmt]
>   | CBreak
>   | CContinue
>   | CReturn CExpr
>   | CLabel String
>   | CGoto String
>   deriving Eq

> data LVar = LVar String | LElem LVar CExpr | LField LVar String deriving Eq
> data CCase = CCase CCaseLabel [CStmt] deriving Eq
> data CCaseLabel =
>   CCaseLabel String | CCaseInt Integer | CCaseDefault deriving Eq

> data CExpr =
>     CNull
>   | CInt Integer
>   | CFloat Double
>   | CString String
>   | CElem CExpr CExpr
>   | CField CExpr String
>   | CFunCall String [CExpr]
>   | CCond CExpr CExpr CExpr
>   | CAdd CExpr CExpr
>   | CSub CExpr CExpr
>   | CMul CExpr CExpr
>   | CDiv CExpr CExpr
>   | CMod CExpr CExpr
>   | CShift CExpr Int
>   | CRel CExpr String CExpr
>   | CAddr CExpr
>   | CCast CType CExpr
>   | CExpr String
>   deriving Eq

> data CType =
>     CType String
>   | CConstType String
>   | CPointerType CType
>   | CConstPointerType CType
>   | CArrayType CType (Maybe Int)
>   | CFunctionType CType [CType]
>   deriving Eq

\end{verbatim}
The function \texttt{mergeCCode} merges the code of two files. In
order to avoid error messages from the C compiler, it removes all
duplicate declarations from the resulting file.
\begin{verbatim}

> mergeCFile :: CFile -> CFile -> CFile
> mergeCFile cf1 cf2 = nub (cf1 ++ cf2)

\end{verbatim}
\input{CPretty.lhs}
