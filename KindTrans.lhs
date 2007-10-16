% -*- LaTeX -*-
% $Id: KindTrans.lhs 2502 2007-10-16 20:10:53Z wlux $
%
% Copyright (c) 2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{KindTrans.lhs}
\section{Kind Transformations}
This module implements transformations between the internal and
external kind representations.
\begin{verbatim}

> module KindTrans(toKind, fromKind, ppKind) where
> import Base
> import CurryPP
> import CurrySyntax
> import Kinds

\end{verbatim}
The function \texttt{toKind} converts a kind expression into a kind.
\begin{verbatim}

> toKind :: KindExpr -> Kind
> toKind Star = KindStar
> toKind (ArrowKind k1 k2) = KindArrow (toKind k1) (toKind k2)

\end{verbatim}
The function \texttt{fromKind} converts a kind into a kind expression.
During the conversion, all kind variables are instantiated with kind
$\star$.
\begin{verbatim}

> fromKind :: Kind -> KindExpr
> fromKind KindStar = Star
> fromKind (KindVariable _) = Star
> fromKind (KindArrow k1 k2) = ArrowKind (fromKind k1) (fromKind k2)

\end{verbatim}
The following function implements pretty-printing for kinds by
converting them into kind expressions.
\begin{verbatim}

> ppKind :: Kind -> Doc
> ppKind = ppKindExpr 0 . fromKind

\end{verbatim}
