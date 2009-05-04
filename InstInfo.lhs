% -*- LaTeX -*-
% $Id: InstInfo.lhs 2815 2009-05-04 13:59:57Z wlux $
%
% Copyright (c) 1999-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{InstInfo.lhs}
\section{Instances}
The compiler maintains information about defined instances in an
environment that maps $C$-$T$ pairs, which associate a type class
identifier and a type constructor identifier, onto the context of the
corresponding instance declaration, the name of the module where the
instance is declared, and the arities of the instance's implementation
methods. A flat environment is sufficient because instances are
visible globally and cannot be hidden. Instance relationships are
recorded only with the original names of the class and type
constructor involved.

\ToDo{Require that instance methods are sorted in the same order as in
  the corresponding type class?}
\begin{verbatim}

> module InstInfo(module InstInfo, CT(..)) where
> import Ident
> import IdentInfo
> import Env
> import TypeInfo
> import Types

> type InstEnv = Env CT InstInfo
> type InstInfo = (ModuleIdent,Context,MethodList)

\end{verbatim}
The initial instance environment \texttt{initIEnv} is empty.
\begin{verbatim}

> initIEnv :: InstEnv
> initIEnv = emptyEnv

\end{verbatim}
