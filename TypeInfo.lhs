% -*- LaTeX -*-
% $Id: TypeInfo.lhs 2515 2007-10-18 10:54:19Z wlux $
%
% Copyright (c) 1999-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{TypeInfo.lhs}
\section{Type Constructors and Type Classes}
For all defined types and type classes, the compiler maintains kind
information. For algebraic data types and renaming types, the compiler
also records all data constructors belonging to that type, and for
alias types, their arity and expanded right hand side type expressions
are saved. Recording the type's arity is necessary for alias types
because the right hand side type expression can have arbitrary kind
and therefore the type synonym's arity cannot be determined from its
own kind. For instance,
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

Importing and exporting algebraic data types and renaming types is
complicated by the fact that the constructors of the type may be
(partially) hidden in the interface. This facilitates the definition
of abstract data types. An abstract type is always represented as a
data type without constructors in the interface regardless of whether
it is defined as a data type or as a renaming type. When only some
constructors of a data type are hidden, those constructors are
replaced by underscores in the interface. Similarly, it is possible to
hide some or all methods of a type class. The hidden methods are
replaced by underscores as well.
\begin{verbatim}

> module TypeInfo where
> import Base
> import Ident
> import Kinds
> import List
> import Monad
> import PredefTypes
> import TopEnv
> import Types

> type TCEnv = TopEnv TypeInfo
> data TypeInfo = DataType QualIdent Kind [Maybe Ident]
>               | RenamingType QualIdent Kind Ident
>               | AliasType QualIdent Int Kind Type
>               | TypeClass QualIdent Kind [QualIdent] [Maybe Ident]
>               | TypeVar Kind
>               deriving Show

> instance Entity TypeInfo where
>   origName (DataType tc _ _) = tc
>   origName (RenamingType tc _ _) = tc
>   origName (AliasType tc _ _ _) = tc
>   origName (TypeClass cls _ _ _) = cls
>   origName (TypeVar _) = internalError "origName TypeVar"
>   merge (DataType tc1 k cs1) (DataType tc2 _ cs2)
>     | tc1 == tc2 = Just (DataType tc1 k (mergeData cs1 cs2))
>     where mergeData cs1 cs2
>             | null cs1 = cs2
>             | null cs2 = cs1
>             | otherwise = zipWith mplus cs1 cs2
>   merge (DataType tc1 k _) (RenamingType tc2 _ nc)
>     | tc1 == tc2 = Just (RenamingType tc1 k nc)
>   merge (RenamingType tc1 k nc) (DataType tc2 _ _)
>     | tc1 == tc2 = Just (RenamingType tc1 k nc)
>   merge (RenamingType tc1 k nc) (RenamingType tc2 _ _)
>     | tc1 == tc2 = Just (RenamingType tc1 k nc)
>   merge (AliasType tc1 n k ty) (AliasType tc2 _ _ _)
>     | tc1 == tc2 = Just (AliasType tc1 n k ty)
>   merge (TypeClass cls1 k clss fs1) (TypeClass cls2 _ _ fs2)
>     | cls1 == cls2 = Just (TypeClass cls1 k clss (zipWith mplus fs1 fs2))
>   merge _ _ = Nothing

\end{verbatim}
The initial type constructor environment \texttt{initTCEnv} is
initialized with the types of the predefined unit, list, and tuple
types.
\begin{verbatim}

> initTCEnv :: TCEnv
> initTCEnv =
>   foldr (uncurry (predefTC . unapplyType True)) emptyTCEnv predefTypes
>   where emptyTCEnv =
>           emptyTopEnv (Just (map (tupleTC . unapplyType True) tupleTypes))
>         predefTC (TypeConstructor tc,tys) cs =
>           predefTopEnv tc (DataType tc k (map (Just . fst) cs))
>           where k = simpleKind (length tys)
>         tupleTC (TypeConstructor tc,tys) = DataType tc k [Just (unqualify tc)]
>           where k = simpleKind (length tys)

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

> constructors :: QualIdent -> TCEnv -> [Maybe Ident]
> constructors tc tcEnv =
>   case qualLookupTopEnv tc tcEnv of
>     [DataType _ _ cs] -> cs
>     [RenamingType _ _ c] -> [Just c]
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

> classMethods :: QualIdent -> TCEnv -> [Maybe Ident]
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
