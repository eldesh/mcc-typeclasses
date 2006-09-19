% -*- LaTeX -*-
% $Id: TypeTrans.lhs 1791 2005-10-09 17:39:51Z wlux $
%
% Copyright (c) 1999-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{TypeTrans.lhs}
\section{Type Transformations}
This module implements transformations between the internal and
external type representations.
\begin{verbatim}

> module TypeTrans(toType, toTypes, fromType,
>                  expandMonoType, expandMonoTypes, expandPolyType,
>                  ppType, ppTypeScheme) where
> import Base
> import CurryPP
> import List
> import Map
> import Pretty
> import TopEnv
> import TypeSubst

\end{verbatim}
The functions \texttt{toType} and \texttt{toTypes} convert Curry type
expressions into types. The compiler uses only correctly qualified
names internally and therefore adds the name of the current module to
all type constructors that lack a module qualifier. Type variables are
assigned ascending indices in the order of their occurrence in the
types. It is possible to pass a list of additional type variables to
both functions, which are assigned indices before those variables
occurring in the type. This allows preserving the order of type
variables in the left hand side of a type declaration.

Note the subtle difference between \texttt{toTypes m tvs tys} and
\texttt{map (toType m tvs) tys}. The former ensures that consistent
indices are assigned to all type variables occurring in the type
expressions \texttt{tys}, whereas the latter assigns type variable
indices independently for each type expression.
\begin{verbatim}

> toType :: ModuleIdent -> [Ident] -> TypeExpr -> Type
> toType m tvs ty = qualifyType m (toType' (enumTypeVars tvs ty) ty)

> toTypes :: ModuleIdent -> [Ident] -> [TypeExpr] -> [Type]
> toTypes m tvs tys = map (qualifyType m . toType' (enumTypeVars tvs tys)) tys

> enumTypeVars :: Expr a => [Ident] -> a -> FM Ident Int
> enumTypeVars tvs ty = fromListFM (zip (tvs ++ tvs') [0..])
>   where tvs' = [tv | tv <- nub (fv ty), tv `notElem` tvs]

> toType' :: FM Ident Int -> TypeExpr -> Type
> toType' tvs (ConstructorType tc tys) =
>   TypeConstructor tc (map (toType' tvs) tys)
> toType' tvs (VariableType tv) =
>   maybe (internalError ("toType " ++ show tv)) TypeVariable (lookupFM tv tvs)
> toType' tvs (TupleType tys) = tupleType (map (toType' tvs) tys)
> toType' tvs (ListType ty) = listType (toType' tvs ty)
> toType' tvs (ArrowType ty1 ty2) =
>   TypeArrow (toType' tvs ty1) (toType' tvs ty2)

> qualifyType :: ModuleIdent -> Type -> Type
> qualifyType m (TypeConstructor tc tys) =
>   TypeConstructor (if isPrimTypeId tc then tc else qualQualify m tc)
>                   (map (qualifyType m) tys)
> qualifyType _ (TypeVariable tv) = TypeVariable tv
> qualifyType m (TypeConstrained tys tv) =
>   TypeConstrained (map (qualifyType m) tys) tv
> qualifyType m (TypeArrow ty1 ty2) =
>   TypeArrow (qualifyType m ty1) (qualifyType m ty2)
> qualifyType _ (TypeSkolem k) = TypeSkolem k

\end{verbatim}
The function \texttt{fromType} converts a type into a Curry type
expression. During the conversion, the compiler removes the module
qualifier from all type constructors defined in the current module.
\begin{verbatim}

> fromType :: ModuleIdent -> Type -> TypeExpr
> fromType m ty = fromType' (unqualifyType m ty)

> fromType' :: Type -> TypeExpr
> fromType' (TypeConstructor tc tys)
>   | isQTupleId tc = TupleType tys'
>   | tc == qListId && length tys == 1 = ListType (head tys')
>   | otherwise = ConstructorType tc tys'
>   where tys' = map (fromType') tys
> fromType' (TypeVariable tv) =
>   VariableType (if tv >= 0 then nameSupply !! tv
>                            else mkIdent ('_' : show (-tv)))
> fromType' (TypeConstrained tys _) = fromType' (head tys)
> fromType' (TypeArrow ty1 ty2) = ArrowType (fromType' ty1) (fromType' ty2)
> fromType' (TypeSkolem k) = VariableType (mkIdent ("_?" ++ show k))

> unqualifyType :: ModuleIdent -> Type -> Type
> unqualifyType m (TypeConstructor tc tys) =
>   TypeConstructor (qualUnqualify m tc) (map (unqualifyType m) tys)
> unqualifyType _ (TypeVariable tv) = TypeVariable tv
> unqualifyType m (TypeConstrained tys tv) =
>   TypeConstrained (map (unqualifyType m) tys) tv
> unqualifyType m (TypeArrow ty1 ty2) =
>   TypeArrow (unqualifyType m ty1) (unqualifyType m ty2)
> unqualifyType m (TypeSkolem k) = TypeSkolem k

\end{verbatim}
The functions \texttt{expandMonoType}, \texttt{expandMonoTypes}, and
\texttt{expandPolyType} convert type expressions into types and also
expand all type synonyms and qualify all type constructors during the
conversion. Qualification and expansion have to be performed at the
same time, since type constructors are recorded in the type
constructor environment using the names visible in the source code,
but the expanded types refer to the original names.
\begin{verbatim}

> expandMonoType :: TCEnv -> [Ident] -> TypeExpr -> Type
> expandMonoType tcEnv tvs ty =
>   expandType tcEnv (toType' (enumTypeVars tvs ty) ty)

> expandMonoTypes :: TCEnv -> [Ident] -> [TypeExpr] -> [Type]
> expandMonoTypes tcEnv tvs tys =
>   map (expandType tcEnv . toType' (enumTypeVars tvs tys)) tys

> expandPolyType :: TCEnv -> TypeExpr -> TypeScheme
> expandPolyType tcEnv ty = polyType $ normalize 0 $ expandMonoType tcEnv [] ty

> expandType :: TCEnv -> Type -> Type
> expandType tcEnv (TypeConstructor tc tys) =
>   case qualLookupTopEnv tc tcEnv of
>     [DataType tc' _ _] -> TypeConstructor tc' tys'
>     [RenamingType tc' _ _] -> TypeConstructor tc' tys'
>     [AliasType _ _ ty] -> expandAliasType tys' ty
>     _ -> internalError ("expandType " ++ show tc)
>   where tys' = map (expandType tcEnv) tys
> expandType _ (TypeVariable tv) = TypeVariable tv
> expandType _ (TypeConstrained tys tv) = TypeConstrained tys tv
> expandType tcEnv (TypeArrow ty1 ty2) =
>   TypeArrow (expandType tcEnv ty1) (expandType tcEnv ty2)
> expandType _ (TypeSkolem k) = TypeSkolem k

\end{verbatim}
The following functions implement pretty-printing for types by
converting them into type expressions.
\begin{verbatim}

> ppType :: ModuleIdent -> Type -> Doc
> ppType m = ppTypeExpr 0 . fromType m

> ppTypeScheme :: ModuleIdent -> TypeScheme -> Doc
> ppTypeScheme m (ForAll _ ty) = ppType m ty

\end{verbatim}
