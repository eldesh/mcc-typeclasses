% -*- LaTeX -*-
% $Id: TypeInfo.lhs 3242 2016-06-19 10:53:21Z wlux $
%
% Copyright (c) 1999-2015, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{TypeInfo.lhs}
\section{Type Constructors and Type Classes}
For all defined types and type classes, the compiler maintains kind
information. For algebraic data types and renaming types, the compiler
also records all data constructors belonging to that type, and for
alias types, their arity and expanded right hand side type expressions
are saved. The constructor lists are used only for the purpose of
creating module interfaces. It is important that the constructors are
ordered in the same way as in the data type's definition. Recording
the type's arity is necessary for alias types because the right hand
side type expression can have arbitrary kind and therefore the type
synonym's arity cannot be determined from its own kind. For instance,
\begin{verbatim}
  type List = []
\end{verbatim}
is explicitly permitted by the revised Haskell'98
report~\cite{PeytonJones03:Haskell} (see Sect.~4.2.2). For type
classes, the names of their immediate super classes and their methods
are saved. The list of super classes is always sorted by their names.
The list of method names also includes the arities of the default
method implementations. Type classes are recorded in the type
constructor environment because type constructors and type classes
share a common name space. For type variables, only their kind is
recorded in the environment.

\ToDo{Sort methods of a type class, too, because their order is not
  relevant?}

Importing and exporting algebraic data types and renaming types is
complicated by the fact that the constructors of the type may be
(partially) hidden in the interface. This facilitates the definition
of abstract data types. An abstract type is always represented as a
data type without constructors in the interface regardless of whether
it is defined as a data type or as a renaming type.
\begin{verbatim}

> module TypeInfo where
> import Base
> import Ident
> import Kinds
> import List
> import TopEnv
> import Types

> type TCEnv = TopEnv TypeInfo
> data TypeInfo = DataType QualIdent Kind [Ident]
>               | RenamingType QualIdent Kind Ident
>               | AliasType QualIdent Int Kind Type
>               | TypeClass QualIdent Kind [QualIdent] MethodList
>               | TypeVar Kind
>               deriving Show
> type MethodList = [(Ident,Int)]

> instance Entity TypeInfo where
>   origName (DataType tc _ _) = tc
>   origName (RenamingType tc _ _) = tc
>   origName (AliasType tc _ _ _) = tc
>   origName (TypeClass cls _ _ _) = cls
>   origName (TypeVar _) = internalError "origName TypeVar"
>   merge (DataType tc1 k1 cs1) (DataType tc2 k2 cs2)
>     | tc1 == tc2 && k1 == k2 && (null cs1 || null cs2 || cs1 == cs2) =
>         Just (DataType tc1 k1 (if null cs1 then cs2 else cs1))
>   merge (DataType tc1 k1 []) (RenamingType tc2 k2 nc)
>     | tc1 == tc2 && k1 == k2 = Just (RenamingType tc1 k1 nc)
>   merge (RenamingType tc1 k1 nc) (DataType tc2 k2 [])
>     | tc1 == tc2 && k1 == k2 = Just (RenamingType tc1 k1 nc)
>   merge (RenamingType tc1 k1 nc1) (RenamingType tc2 k2 nc2)
>     | tc1 == tc2 && k1 == k2 && nc1 == nc2 = Just (RenamingType tc1 k1 nc1)
>   merge (AliasType tc1 n1 k1 ty1) (AliasType tc2 n2 k2 ty2)
>     | tc1 == tc2 && n1 == n2 && k1 == k2 && ty1 == ty2 =
>         Just (AliasType tc1 n1 k1 ty1)
>   merge (TypeClass cls1 k1 clss1 fs1) (TypeClass cls2 k2 clss2 fs2)
>     | cls1 == cls2 && k1 == k2 && clss1 == clss2 &&
>       (null fs1 || null fs2 || fs1 == fs2) =
>         Just (TypeClass cls1 k1 clss1 (if null fs1 then fs2 else fs1))
>   merge _ _ = Nothing

\end{verbatim}
The initial type constructor environment \texttt{initTCEnv} is empty.
\begin{verbatim}

> initTCEnv :: TCEnv
> initTCEnv = emptyTopEnv

\end{verbatim}
The function \texttt{constrKind} returns the kind of a type
constructor from the type constructor environment and the function
\texttt{constructors} returns the names of the data and newtype
constructors of a type. The function \texttt{typeAlias} returns the
right hand side type from the definition of a type synonym and
\texttt{Nothing} for all other types. All these functions
are supposed to be used only after checking for undefined and
ambiguous type identifiers and therefore should not fail.
\begin{verbatim}

> constrKind :: QualIdent -> TCEnv -> Kind
> constrKind tc tcEnv =
>   case qualLookupTopEnv tc tcEnv of
>     [DataType _ k _] -> k
>     [RenamingType _ k _] -> k
>     [AliasType _ _ k _] -> k
>     _ -> internalError ("constrKind " ++ show tc)

> constructors :: QualIdent -> TCEnv -> [Ident]
> constructors tc tcEnv =
>   case qualLookupTopEnv tc tcEnv of
>     [DataType _ _ cs] -> cs
>     [RenamingType _ _ c] -> [c]
>     [AliasType _ _ _ _] -> []
>     _ -> internalError ("constructors " ++ show tc)

> typeAlias :: QualIdent -> TCEnv -> Maybe (Int,Type)
> typeAlias tc tcEnv =
>   case qualLookupTopEnv tc tcEnv of
>     [DataType _ _ _] -> Nothing
>     [RenamingType _ _ _] -> Nothing
>     [AliasType _ n _ ty] -> Just (n,ty)
>     _ -> internalError ("typeAlias " ++ show tc)

\end{verbatim}
The function \texttt{classKind} returns the kind of a type class'
instance type from the type environment. The function
\texttt{superClasses} returns a list of all immediate super classes of
a type class. The function \texttt{allSuperClasses} returns a list of
all direct and indirect super classes of a class including the class
itself, i.e., it computes the reflexive transitive closure of
\texttt{superClasses}. The function \texttt{classMethods} returns the
methods defined by a class.
\begin{verbatim}

> classKind :: QualIdent -> TCEnv -> Kind
> classKind tc tcEnv =
>   case qualLookupTopEnv tc tcEnv of
>     [TypeClass _ k _ _] -> k
>     _ -> internalError ("classKind " ++ show tc)

> superClasses :: QualIdent -> TCEnv -> [QualIdent]
> superClasses cls clsEnv =
>   case qualLookupTopEnv cls clsEnv of
>     [TypeClass _ _ clss _] -> clss
>     _ -> internalError ("superClasses " ++ show cls)

> allSuperClasses :: QualIdent -> TCEnv -> [QualIdent]
> allSuperClasses cls clsEnv = nub (classes cls)
>   where classes cls = cls : concatMap classes (superClasses cls clsEnv)

> classMethods :: QualIdent -> TCEnv -> MethodList
> classMethods cls clsEnv =
>   case qualLookupTopEnv cls clsEnv of
>     [TypeClass _ _ _ fs] -> fs
>     _ -> internalError ("classMethods " ++ show cls)

\end{verbatim}
The function \texttt{varKind} returns the kind of a type variable.
\begin{verbatim}

> varKind :: Ident -> TCEnv -> Kind
> varKind tc tcEnv =
>   case lookupTopEnv tc tcEnv of
>     [TypeVar k] -> k
>     _ -> internalError ("varKind " ++ show tc)

\end{verbatim}
