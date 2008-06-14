% -*- LaTeX -*-
% $Id: PrecInfo.lhs 2725 2008-06-14 17:24:48Z wlux $
%
% Copyright (c) 1999-2008, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{PrecInfo.lhs}
\section{Operator Precedences}
In order to parse infix expressions correctly, the compiler must know
the precedence and associativity of each operator. Operator
precedences are associated with entities and are checked after
renaming. If no fixity is assigned to an operator, it is given the
default precedence 9 and assumed to be a left-associative operator.
\begin{verbatim}

> module PrecInfo where
> import Curry
> import TopEnv

> data OpPrec = OpPrec Infix Integer deriving Eq

> instance Show OpPrec where
>   showsPrec _ (OpPrec fix p) = showString (assoc fix) . shows p
>     where assoc InfixL = "left "
>           assoc InfixR = "right "
>           assoc Infix  = "non-assoc "

> defaultPrec :: OpPrec
> defaultPrec = OpPrec InfixL defaultP

> defaultP :: Integer
> defaultP = 9

\end{verbatim}
Operator precedences that are different from the default are recorded
in the precedence environment. A top-level environment is sufficient
because precedences are checked after renaming.
\begin{verbatim}

> type PEnv = TopEnv PrecInfo
> data PrecInfo = PrecInfo QualIdent OpPrec deriving (Eq,Show)

> instance Entity PrecInfo where
>   origName (PrecInfo op _) = op
>   merge p1 p2
>     | p1 == p2 = Just p1
>     | otherwise = Nothing

\end{verbatim}
The initial precedence environment \texttt{initPEnv} is empty.
\begin{verbatim}

> initPEnv :: PEnv
> initPEnv = emptyTopEnv

\end{verbatim}
