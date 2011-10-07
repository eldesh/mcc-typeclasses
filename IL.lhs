% -*- LaTeX -*-
% $Id: IL.lhs 3056 2011-10-07 16:27:03Z wlux $
%
% Copyright (c) 1999-2011 Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{IL.lhs}
\section{The Intermediate Language}\label{sec:IL}
The module \texttt{IL} defines the intermediate language, which will
be compiled into abstract machine code. The intermediate language
removes a lot of syntactic sugar from the Curry source
language. Top-level declarations are restricted to data type, type
synonym, and function definitions. Type synonyms are remnants of
newtype declarations in the source code. Their sole purpose is to
allow type reconstruction while preserving the invariant that the
arity of every function matches its apparent type. Note that the
debugging transformation, which is described in
Sect.~\ref{sec:dtrans}, currently relies on this invariant. Each
intermediate language module has an export list that names the
exported data constructors and functions defined by that module.

Type declarations use a de-Bruijn indexing scheme (starting at 0) for
type variables. In the type of a function, all type variables are
numbered in the order of their occurrence from left to right, i.e., a
type \texttt{(Int -> b) -> (a,b) -> c -> (a,c)} is translated into the
type (using integer numbers to denote type variables)
\texttt{(Int -> 0) -> (1,0) -> 2 -> (1,2)}.

Pattern matching in equations is handled by rigid \texttt{case} and
flexible \texttt{fcase} expressions. \texttt{(F)case} expressions
always evaluate the scrutinized expression to head normal form. Note
that their semantics thus differs from Curry source code where the
expression \texttt{case e1 of \char`\{\ x -> e2 \char`\}} is
equivalent to \texttt{let \char`\{\ x = e1 \char`\}\ in e2}.
Overlapping rules are translated with the help of \texttt{choice}
expressions. The intermediate language has three kinds of binding
expressions: \texttt{Exist} expressions introduce new logical
variables, \texttt{let} expressions introduce multiple, non-recursive
variable bindings, and \texttt{letrec} expressions introduce multiple
possibly mutually recursive variable bindings. The intermediate
language explicitly distinguishes (local) variables and (global)
functions in expressions.
\begin{verbatim}

> module IL(module IL,module Ident) where
> import Ident

> data Module =
>   Module ModuleIdent [QualIdent] [ModuleIdent] [Decl]
>   deriving (Eq,Show)

> data Decl =
>     DataDecl QualIdent Int [ConstrDecl]
>   | TypeDecl QualIdent Int Type
>   | FunctionDecl QualIdent [Ident] Type Expression
>   | ForeignDecl QualIdent CallConv String Type
>   deriving (Eq,Show)

> data ConstrDecl = ConstrDecl QualIdent [Type] deriving (Eq,Show)
> data CallConv = Primitive | CCall | RawCall deriving (Eq,Show)

> data Type =
>     TypeConstructor QualIdent [Type]
>   | TypeVariable Int
>   | TypeArrow Type Type
>   deriving (Eq,Show)

> data Literal =
>     Char Char
>   | Int Integer
>   | Integer Integer
>   | Float Double
>   deriving (Eq,Show)

> data ConstrTerm =
>   -- literal patterns
>     LiteralPattern Literal
>   -- constructors
>   | ConstructorPattern QualIdent [Ident]
>   -- default
>   | VariablePattern Ident
>   deriving (Eq,Show)

> data Expression =
>   -- literal constants
>     Literal Literal
>   -- variables, functions, constructors
>   | Variable Ident | Function QualIdent Int | Constructor QualIdent Int
>   -- applications
>   | Apply Expression Expression
>   -- case expressions
>   | Case Eval Expression [Alt]
>   -- non-determinisismic choice
>   | Choice [Expression]
>   -- binding forms
>   | Exist [Ident] Expression
>   | Let Rec [Binding] Expression
>   -- source code location annotations
>   | SrcLoc String Expression
>   deriving (Eq,Show)

> data Eval = Rigid | Flex deriving (Eq,Show)
> data Rec = NonRec | Rec deriving (Eq,Show)
> data Alt = Alt ConstrTerm Expression deriving (Eq,Show)
> data Binding = Binding Ident Expression deriving (Eq,Show)

\end{verbatim}
