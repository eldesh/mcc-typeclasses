% -*- LaTeX -*-
% $Id: IdentInfo.lhs 2691 2008-05-01 22:08:36Z wlux $
%
% Copyright (c) 1999-2008, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{IdentInfo.lhs}
\section{Type and Value Identifiers}
In order to implement syntax checking, we use two environments that
map type and value identifiers on their kinds.
\begin{verbatim}

> module IdentInfo where
> import Ident
> import List
> import NestEnv
> import PredefTypes
> import Set
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
>   merge (Data tc1 cs1) (Data tc2 cs2)
>     | tc1 == tc2 = Just (Data tc1 (cs1 `union` cs2))
>     | otherwise = Nothing
>   merge (Data _ _) (Alias _) = Nothing
>   merge (Data _ _) (Class _ _) = Nothing
>   merge (Alias _) (Data _ _) = Nothing
>   merge (Alias tc1) (Alias tc2)
>     | tc1 == tc2 = Just (Alias tc1)
>     | otherwise = Nothing
>   merge (Alias _) (Class _ _) = Nothing
>   merge (Class _ _) (Data _ _) = Nothing
>   merge (Class _ _) (Alias _) = Nothing
>   merge (Class cls1 fs1) (Class cls2 fs2)
>     | cls1 == cls2 = Just (Class cls1 (fs1 `union` fs2))
>     | otherwise = Nothing

> initTEnv :: TypeEnv
> initTEnv = foldr (uncurry (predefType . rootOfType)) emptyTEnv predefTypes
>   where emptyTEnv =
>           emptyTopEnv (Just (map (tupleType . rootOfType) tupleTypes))
>         predefType tc cs =
>           predefTopEnv tc (Data tc (map (unqualify . fst) cs))
>         tupleType tc = Data tc [unqualify tc]

\end{verbatim}
When checking for duplicate instance declarations, the compiler uses a
set of $C$-$T$ pairs, which contains one element for each defined or
imported instance. Instances are recorded only for the original names
of the type class and type constructor involved. The initial instance
set \texttt{instISet} is empty.
\begin{verbatim}

> data CT = CT QualIdent QualIdent deriving (Eq,Ord,Show)
> type InstSet = Set CT

> initISet :: InstSet
> initISet = zeroSet

\end{verbatim}
At pattern and expression level, we distinguish constructors on one
side and functions (including type class methods) and variables on the
other side. Field labels are represented as variables here, too. Each
variable has an associated list of identifiers, which contains the
names of all constructors for which the variable is also a valid field
label. We use the original names of the constructors because the
import paths of the constructors and labels are not relevant.

Since scopes can be nested in source code, we use a nested environment
for checking source modules and goals, whereas a flat top-level
environment is sufficient for checking import and export declarations.
The initial value identifier environment \texttt{initVEnv} is
initialized with the data constructors of the predefined unit, list,
and tuple types.
\begin{verbatim}

> type FunEnv = TopEnv ValueKind
> type VarEnv = NestEnv ValueKind

> data ValueKind =
>     Constr QualIdent
>   | Var QualIdent [QualIdent]
>   deriving (Eq,Show)

> instance Entity ValueKind where
>   origName (Constr c) = c
>   origName (Var x _) = x
>   merge (Constr c1) (Constr c2)
>     | c1 == c2 = Just (Constr c1)
>     | otherwise = Nothing
>   merge (Constr _) (Var _ _) = Nothing
>   merge (Var _ _) (Constr _) = Nothing
>   merge (Var v1 cs1) (Var v2 cs2)
>     | v1 == v2 = Just (Var v1 (cs1 `union` cs2))
>     | otherwise = Nothing

> initVEnv :: FunEnv
> initVEnv = foldr (predefCon . fst) emptyVEnv (concatMap snd predefTypes)
>   where emptyVEnv = emptyTopEnv (Just (map (Constr . rootOfType) tupleTypes))
>         predefCon c = predefTopEnv c (Constr c)

\end{verbatim}
