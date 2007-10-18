% -*- LaTeX -*-
% $Id: InstInfo.lhs 2514 2007-10-18 10:43:08Z wlux $
%
% Copyright (c) 1999-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{InstInfo.lhs}
\section{Instances}
The compiler maintains information about defined instances in an
environment that maps $C$-$T$-pairs, which associate a type class
identifier and a type constructor identifier, onto the context of the
corresponding instance declaration and the name of the module where
the instance is declared. A flat environment is sufficient because
instances are visible globally and cannot be hidden. Instance
relationships are recorded only with the original names of the class
and type constructor involved.
\begin{verbatim}

> module InstInfo(module InstInfo, CT(..)) where
> import Ident
> import IdentInfo
> import Env
> import Types

> type InstEnv = Env CT (ModuleIdent,Context)

\end{verbatim}
 The initial instance environment \texttt{initIEnv} is empty.
\begin{verbatim}

> initIEnv :: InstEnv
> initIEnv = emptyEnv

\end{verbatim}
