% -*- LaTeX -*-
% $Id: IL.lhs 1817 2005-11-06 23:42:07Z wlux $
%
% Copyright (c) 1999-2005 Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{IL.lhs}
\section{The Intermediate Language}\label{sec:IL}
The module \texttt{IL} defines the intermediate language which will be
compiled into abstract machine code. The intermediate language removes
a lot of syntactic sugar from the Curry source language. Top-level
declarations are restricted to data type, type synonym, and function
definitions. Type synonyms are remnants of newtype declarations in the
source code. Their sole purpose is to allow type reconstruction while
preserving the invariant that the arity of every function matches its
apparent type. Note that the debugging transformation, which is
described in Sect.~\ref{sec:dtrans}, currently relies on this
invariant.

Type declarations use a de-Bruijn indexing scheme (starting at 0) for
type variables. In the type of a function, all type variables are
numbered in the order of their occurence from left to right, i.e., a
type \texttt{(Int -> b) -> (a,b) -> c -> (a,c)} is translated into the
type (using integer numbers to denote the type variables)
\texttt{(Int -> 0) -> (1,0) -> 2 -> (1,2)}.

Pattern matching in equations is handled via flexible and rigid
\texttt{Case} expressions. Overlapping rules are translated with the
help of \texttt{Or} expressions. The intermediate language has three
kinds of binding expressions, \texttt{Exist} expressions introduce a
new logical variable, \texttt{Let} expression support a single
non-recursive variable binding, and \texttt{Letrec} expressions
introduce multiple variables with recursive initializer expressions.
The intermediate language explicitly distinguishes (local) variables
and (global) functions in expressions.
\begin{verbatim}

> module IL where
> import Ident

> data Module = Module ModuleIdent [ModuleIdent] [Decl] deriving (Eq,Show)

> data Decl = 
>     DataDecl QualIdent Int [ConstrDecl]
>   | TypeDecl QualIdent Int Type
>   | FunctionDecl QualIdent [Ident] Type Expression
>   | ForeignDecl QualIdent CallConv String Type
>   deriving (Eq,Show)

> data ConstrDecl = ConstrDecl QualIdent [Type] deriving (Eq,Show)
> data CallConv = Primitive | CCall deriving (Eq,Show)

> data Type =
>     TypeConstructor QualIdent [Type]
>   | TypeVariable Int
>   | TypeArrow Type Type
>   deriving (Eq,Show)

> data Literal = Char Char | Int Int | Float Double deriving (Eq,Show)

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
>   -- non-determinisismic or
>   | Or Expression Expression
>   -- binding forms
>   | Exist Ident Expression
>   | Let Binding Expression
>   | Letrec [Binding] Expression
>   deriving (Eq,Show)

> data Eval = Rigid | Flex deriving (Eq,Show)
> data Alt = Alt ConstrTerm Expression deriving (Eq,Show)
> data Binding = Binding Ident Expression deriving (Eq,Show)

\end{verbatim}
