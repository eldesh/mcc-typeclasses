% -*- LaTeX -*-
% $Id: IdentInfo.lhs 2513 2007-10-18 09:50:08Z wlux $
%
% Copyright (c) 1999-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{IdentInfo.lhs}
\section{Type and Value Identifiers}
In order to implement syntax checking, we use two environments that
map type and value identifiers on their kinds.
\begin{verbatim}

> module IdentInfo where
> import Base
> import Ident
> import NestEnv
> import TopEnv
> import Types

\end{verbatim}
At the type level, we distinguish data and renaming types, synonym
types, and type classes. Type variables are not recorded. Type
synonyms use a kind of their own so that the compiler can verify that
no type synonyms are used in type expressions in interface files. The
initial type identifier environment \texttt{initTEnv} is initialized
with the type constructors of the predefined unit, list, and tuple
types.
\begin{verbatim}

> type TypeEnv = TopEnv TypeKind
> data TypeKind =
>     Data QualIdent [Ident]
>   | Alias QualIdent
>   | Class QualIdent [Ident]
>   deriving (Eq,Show)

> instance Entity TypeKind where
>   origName (Data tc _) = tc
>   origName (Alias tc) = tc
>   origName (Class cls _) = cls

> initTEnv :: TypeEnv
> initTEnv = foldr (uncurry (predefType . rootOfType)) emptyTEnv predefTypes
>   where emptyTEnv =
>           emptyTopEnv (Just (map (tupleType . rootOfType) tupleTypes))
>         predefType tc cs = predefTopEnv tc (Data tc (map fst cs))
>         tupleType tc = Data tc [unqualify tc]

\end{verbatim}
At pattern and expression level, we distinguish constructors on one
side and functions (including type class methods) and variables on the
other side. Since scopes can be nested in source code, we use a nested
environment for checking source modules and goals, whereas a flat
top-level environment is sufficient for checking import and export
declarations. The initial value identifier environment
\texttt{initVEnv} is initialized with the data constructors of the
predefined unit, list, and tuple types.
\begin{verbatim}

> type FunEnv = TopEnv ValueKind
> type VarEnv = NestEnv ValueKind
> data ValueKind = Constr QualIdent | Var QualIdent deriving (Eq,Show)

> instance Entity ValueKind where
>   origName (Constr c) = c
>   origName (Var x) = x

> initVEnv :: FunEnv
> initVEnv =
>   foldr (predefCon . qualify . fst) emptyVEnv (concatMap snd predefTypes)
>   where emptyVEnv = emptyTopEnv (Just (map (Constr . rootOfType) tupleTypes))
>         predefCon c = predefTopEnv c (Constr c)

\end{verbatim}
