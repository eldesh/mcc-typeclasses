% -*- LaTeX -*-
% $Id: TypeTrans.lhs 2015 2006-11-21 09:16:28Z wlux $
%
% Copyright (c) 1999-2006, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{TypeTrans.lhs}
\section{Type Transformations}
This module implements transformations between the internal and
external type representations.
\begin{verbatim}

> module TypeTrans(toType, toTypes, toQualType, toTypeScheme,
>                  fromType, fromQualType,
>                  expandMonoType, expandMonoTypes, expandPolyType,
>                  ppType, ppQualType, ppTypeScheme) where
> import Base
> import CurryPP
> import List
> import Map
> import Maybe
> import Pretty
> import TopEnv
> import TypeSubst

\end{verbatim}
The functions \texttt{toType} and \texttt{toTypes} convert Curry type
expressions into types. The functions \texttt{toQualType} and
\texttt{toTypeScheme} similarly convert a qualified type expression
into a qualified type and a type scheme, respectively. The compiler
uses only correctly qualified names internally and therefore adds the
name of the current module to all type constructors and type classes
that lack a module qualifier. Type variables are assigned ascending
indices in the order of their occurrence in the types. It is possible
to pass a list of additional type variables to these functions, which
are assigned indices before those variables occurring in the type.
This allows preserving the order of type variables in the left hand
side of a type declaration and in the head of a type class
declaration, respectively.

Note the subtle difference between \texttt{toTypes m tvs tys} and
\texttt{map (toType m tvs) tys}. The former ensures that consistent
indices are assigned to all type variables occurring in the type
expressions \texttt{tys}, whereas the latter assigns type variable
indices independently in each type expression.
\begin{verbatim}

> toType :: ModuleIdent -> [Ident] -> TypeExpr -> Type
> toType m tvs ty = qualifyType m (toType' (enumTypeVars tvs ty) ty)

> toTypes :: ModuleIdent -> [Ident] -> [TypeExpr] -> [Type]
> toTypes m tvs tys = map (qualifyType m . toType' (enumTypeVars tvs tys)) tys

> toQualType :: ModuleIdent -> [Ident] -> QualTypeExpr -> QualType
> toQualType m tvs ty = qualifyQualType m (toQualType' (enumTypeVars tvs ty) ty)

> toTypeScheme :: ModuleIdent -> QualTypeExpr -> TypeScheme
> toTypeScheme m ty = typeScheme (toQualType m [] ty)

> enumTypeVars :: Expr a => [Ident] -> a -> FM Ident Int
> enumTypeVars tvs ty = fromListFM (zip (tvs ++ tvs') [0..])
>   where tvs' = [tv | tv <- nub (fv ty), tv `notElem` tvs]

> toQualType' :: FM Ident Int -> QualTypeExpr -> QualType
> toQualType' tvs (QualTypeExpr cx ty) =
>   canonType (QualType (nub (map (toTypePred' tvs) cx)) (toType' tvs ty))

> toTypePred' :: FM Ident Int -> ClassAssert -> TypePred
> toTypePred' tvs (ClassAssert cls tv) =
>   TypePred cls (toType' tvs (VariableType tv))

> toType' :: FM Ident Int -> TypeExpr -> Type
> toType' tvs (ConstructorType tc tys) =
>   TypeConstructor tc (map (toType' tvs) tys)
> toType' tvs (VariableType tv) =
>   maybe (internalError ("toType " ++ show tv)) TypeVariable (lookupFM tv tvs)
> toType' tvs (TupleType tys) = tupleType (map (toType' tvs) tys)
> toType' tvs (ListType ty) = listType (toType' tvs ty)
> toType' tvs (ArrowType ty1 ty2) =
>   TypeArrow (toType' tvs ty1) (toType' tvs ty2)

> qualifyQualType :: ModuleIdent -> QualType -> QualType
> qualifyQualType m (QualType cx ty) =
>   QualType (map (qualifyTypePred m) cx) (qualifyType m ty)

> qualifyTypePred :: ModuleIdent -> TypePred -> TypePred
> qualifyTypePred m (TypePred cls ty) =
>   TypePred (qualQualify m cls) (qualifyType m ty)

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
The functions \texttt{fromType} and \texttt{fromQualType} convert a
(qualified) type into a (qualified) Curry type expression. During the
conversion, the compiler removes the module qualifier from all type
constructors and type classes defined in the current module.
\begin{verbatim}

> fromType :: ModuleIdent -> Type -> TypeExpr
> fromType m ty = fromType' (unqualifyType m ty)

> fromQualType :: ModuleIdent -> QualType -> QualTypeExpr
> fromQualType m ty = fromQualType' (unqualifyQualType m ty)

> fromQualType' :: QualType -> QualTypeExpr
> fromQualType' (QualType cx ty) =
>   QualTypeExpr (map fromTypePred' cx) (fromType' ty)

> fromTypePred' :: TypePred -> ClassAssert
> fromTypePred' (TypePred cls ty) =
>   case fromType' ty of
>     VariableType tv -> ClassAssert cls tv
>     _ -> internalError ("fromTypePred " ++ show ty)

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

> unqualifyQualType :: ModuleIdent -> QualType -> QualType
> unqualifyQualType m (QualType cx ty) =
>   QualType (map (unqualifyTypePred m) cx) (unqualifyType m ty)

> unqualifyTypePred :: ModuleIdent -> TypePred -> TypePred
> unqualifyTypePred m (TypePred cls ty) =
>   TypePred (qualUnqualify m cls) (unqualifyType m ty)

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
\texttt{expandPolyType} convert (qualified) type expressions into
(qualified) types and also expand all type synonyms and qualify all
type constructors during the conversion. Qualification and expansion
have to be performed at the same time since type constructors are
recorded in the type constructor environment using the names visible
in the source code, but the expanded types refer to the original
names.
\begin{verbatim}

> expandMonoType :: TCEnv -> [Ident] -> TypeExpr -> Type
> expandMonoType tcEnv tvs ty =
>   expandType tcEnv (toType' (enumTypeVars tvs ty) ty)

> expandMonoTypes :: TCEnv -> [Ident] -> [TypeExpr] -> [Type]
> expandMonoTypes tcEnv tvs tys =
>   map (expandType tcEnv . toType' (enumTypeVars tvs tys)) tys

> expandPolyType :: TCEnv -> QualTypeExpr -> TypeScheme
> expandPolyType tcEnv (QualTypeExpr cx ty) =
>   typeScheme $ normalize 0 $ QualType cx' ty'
>   where cx' = nub (map (expandTypePred tcEnv . toTypePred' tvs) cx)
>         ty' = expandType tcEnv (toType' tvs ty)
>         tvs = enumTypeVars [] ty

> expandTypePred :: TCEnv -> TypePred -> TypePred
> expandTypePred tcEnv (TypePred cls ty) =
>   case qualLookupTopEnv cls tcEnv of
>     [TypeClass cls' _] -> TypePred cls' (expandType tcEnv ty)
>     _ -> internalError ("expandTypePred " ++ show cls)

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

> ppQualType :: ModuleIdent -> QualType -> Doc
> ppQualType m = ppQualTypeExpr . fromQualType m

> ppTypeScheme :: ModuleIdent -> TypeScheme -> Doc
> ppTypeScheme m (ForAll _ ty) = ppQualType m ty

\end{verbatim}
