% -*- LaTeX -*-
% $Id: Kinds.lhs 2088 2007-02-05 09:27:49Z wlux $
%
% Copyright (c) 2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Kinds.lhs}
\section{Kinds}
This module provides the definitions for the internal representation
of kinds in the compiler.
\begin{verbatim}

> module Kinds where

\end{verbatim}
A kind is either $\star$, which is the kind of a value's type, a kind
variable, or an arrow kind. Kind variables are used internally during
kind inference. Kind variables are not supported in Curry kind
expressions and all kind variables that remain free after kind
inference are instantiated to $\star$.
\begin{verbatim}

> data Kind =
>     KindStar
>   | KindVariable Int
>   | KindArrow Kind Kind
>   deriving (Eq,Show)

\end{verbatim}
The function \texttt{kindArity} returns the arity $n$ of a kind $k_1
\rightarrow \dots \rightarrow k_n \rightarrow k_{n+1}$ ($n\geq0$).
\begin{verbatim}

> kindArity :: Kind -> Int
> kindArity KindStar = 0
> kindArity (KindVariable _) = 0
> kindArity (KindArrow _ k) = 1 + kindArity k

\end{verbatim}
The function \texttt{kindVars} returns a list of all kind variables
occurring in a kind $k$.
\begin{verbatim}

> kindVars :: Kind -> [Int]
> kindVars k = vars k []
>   where vars KindStar kvs = kvs
>         vars (KindVariable kv) kvs = kv : kvs
>         vars (KindArrow k1 k2) kvs = vars k1 (vars k2 kvs)

\end{verbatim}
The function \texttt{defaultKind} instantiates all kind variables
occurring in a kind to $\star$.
\begin{verbatim}

> defaultKind :: Kind -> Kind
> defaultKind KindStar = KindStar
> defaultKind (KindVariable _) = KindStar
> defaultKind (KindArrow k1 k2) = KindArrow (defaultKind k1) (defaultKind k2)

\end{verbatim}
The function \texttt{simpleKind} returns the kind of a type
constructor with arity $n$ whose arguments all have kind $\star$. The
predicate \texttt{isSimpleKind} checks whether its argument has the
form returned by \texttt{simpleKind}, i.e., $k = \star \rightarrow
\dots \rightarrow \star$.
\begin{verbatim}

> simpleKind :: Int -> Kind
> simpleKind n = foldr KindArrow KindStar (replicate n KindStar)

> isSimpleKind :: Kind -> Bool
> isSimpleKind KindStar = True
> isSimpleKind (KindVariable _) = False
> isSimpleKind (KindArrow k1 k2) = k1 == KindStar && isSimpleKind k2

\end{verbatim}
