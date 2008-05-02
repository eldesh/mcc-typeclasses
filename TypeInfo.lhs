% -*- LaTeX -*-
% $Id: TypeInfo.lhs 2692 2008-05-02 13:22:41Z wlux $
%
% Copyright (c) 1999-2008, Wolfgang Lux
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
are saved. The list of super classes is always sorted according to
their names. Type classes are recorded in the type constructor
environment because type constructors and type classes share a common
name space. For type variables, only their kind is recorded in the
environment.

\ToDo{Sort methods of a type class, too, because their order is not
  relevant?}

Importing and exporting algebraic data types is complicated by the
fact that the constructors of the type may be (partially) hidden in
the interface. This facilitates the definition of abstract data types.
An abstract type is always represented as a data type without
constructors in the interface.
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
>               | TypeClass QualIdent Kind [QualIdent] [Ident]
>               | TypeVar Kind
>               deriving Show

> instance Entity TypeInfo where
>   origName (DataType tc _ _) = tc
>   origName (RenamingType tc _ _) = tc
>   origName (AliasType tc _ _ _) = tc
>   origName (TypeClass cls _ _ _) = cls
>   origName (TypeVar _) = internalError "origName TypeVar"

\end{verbatim}
The initial type constructor environment \texttt{initTCEnv} is empty.
\begin{verbatim}

> initTCEnv :: TCEnv
> initTCEnv = emptyTopEnv

\end{verbatim}
The function \texttt{constrKind} returns the kind of a type
constructor from the type constructor environment and the function
\texttt{constructors} returns the names of the data and newtype
constructors of a type. Both functions are supposed to be used only
after checking for undefined and ambiguous type identifiers and
therefore should not fail.
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

> aliasArity :: QualIdent -> TCEnv -> Maybe Int
> aliasArity tc tcEnv =
>   case qualLookupTopEnv tc tcEnv of
>     [DataType _ _ _] -> Nothing
>     [RenamingType _ _ _] -> Nothing
>     [AliasType _ n _ _] -> Just n
>     _ -> internalError ("aliasArity " ++ show tc)

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

> classMethods :: QualIdent -> TCEnv -> [Ident]
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
