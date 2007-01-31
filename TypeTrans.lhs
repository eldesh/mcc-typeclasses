% -*- LaTeX -*-
% $Id: TypeTrans.lhs 2085 2007-01-31 16:59:53Z wlux $
%
% Copyright (c) 1999-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{TypeTrans.lhs}
\section{Type Transformations}
This module implements transformations between the internal and
external type representations.
\begin{verbatim}

> module TypeTrans(toType, toTypes, toQualType, toConstrType, toMethodType,
>                  fromType, fromQualType,
>                  expandMonoType, expandConstrType, expandMethodType,
>                  expandPolyType, minContext, maxContext,
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
expressions into types. The function \texttt{toQualType} similarly
converts a qualified type expression into a qualified type.

The function \texttt{toConstrType} returns the type of a data or
newtype constructor. It computes the constructor's type from the
context, type name, and type variables from the left hand side of the
type declaration and the constructor's argument types. A special
feature of this function is that it restricts the context to those
type variables which are free in the argument types as specified in
Sect.~4.2.1 of the revised Haskell'98
report~\cite{PeytonJones03:Haskell}.

The function \texttt{toMethodType} returns the type of a type class
method. It adds the implicit type class constraint to the method's
type signature and ensures that the class' type variable is always
assigned index 0.

The compiler uses only correctly qualified names internally and
therefore adds the name of the current module to all type constructors
and type classes that lack a module qualifier. Type variables are
assigned ascending indices in the order of their occurrence in the
types. It is possible to pass a list of additional type variables to
these functions, which are assigned indices before those variables
occurring in the type.  This allows preserving the order of type
variables in the left hand side of a type declaration and in the head
of a type class declaration, respectively.

Note the subtle difference between \texttt{toTypes m tvs tys} and
\texttt{map (toType m tvs) tys}. The former ensures that consistent
indices are assigned to all type variables occurring in the type
expressions \texttt{tys}, whereas the latter assigns type variable
indices independently in each type expression.
\begin{verbatim}

> toType :: ModuleIdent -> [Ident] -> TypeExpr -> Type
> toType m tvs ty = qualifyType m (toType' tvs ty)

> toTypes :: ModuleIdent -> [Ident] -> [TypeExpr] -> [Type]
> toTypes m tvs tys = map (qualifyType m . toType'' (enumTypeVars tvs tys)) tys

> toQualType :: ModuleIdent -> QualTypeExpr -> QualType
> toQualType m ty = qualifyQualType m (toQualType' ty)

> toConstrType :: ModuleIdent -> [ClassAssert] -> QualIdent -> [Ident]
>              -> [TypeExpr] -> QualType
> toConstrType m cx tc tvs tys = qualifyQualType m (toConstrType' cx tc tvs tys)

> toMethodType :: ModuleIdent -> QualIdent -> Ident -> QualTypeExpr -> QualType
> toMethodType m cls tv ty = qualifyQualType m (toMethodType' cls tv ty)

> toType' :: [Ident] -> TypeExpr -> Type
> toType' tvs ty = toType'' (enumTypeVars tvs ty) ty

> toQualType' :: QualTypeExpr -> QualType
> toQualType' ty = toQualType'' (enumTypeVars [] ty) ty

> toConstrType' :: [ClassAssert] -> QualIdent -> [Ident] -> [TypeExpr]
>               -> QualType
> toConstrType' cx tc tvs tys = toQualType'' tvs' (QualTypeExpr cx' ty')
>   where tvs' = enumTypeVars tvs tys
>         cx' = restrictContext tys cx
>         ty' = foldr ArrowType ty0 tys
>         ty0 = foldl ApplyType (ConstructorType tc) (map VariableType tvs)

> toMethodType' :: QualIdent -> Ident -> QualTypeExpr -> QualType
> toMethodType' cls tv (QualTypeExpr cx ty) =
>   toQualType'' tvs (QualTypeExpr (ClassAssert cls tv : cx) ty)
>   where tvs = enumTypeVars [tv] (QualTypeExpr cx ty)

> enumTypeVars :: Expr a => [Ident] -> a -> FM Ident Int
> enumTypeVars tvs ty = fromListFM (zip (tvs ++ tvs') [0..])
>   where tvs' = [tv | tv <- nub (fv ty), tv `notElem` tvs]

> restrictContext :: [TypeExpr] -> [ClassAssert] -> [ClassAssert]
> restrictContext tys cx =
>   [ClassAssert cls tv | ClassAssert cls tv <- cx, tv `elem` tvs'']
>   where tvs'' = nub (fv tys)

> toQualType'' :: FM Ident Int -> QualTypeExpr -> QualType
> toQualType'' tvs (QualTypeExpr cx ty) =
>   QualType (nub (map (toTypePred'' tvs) cx)) (toType'' tvs ty)

> toTypePred'' :: FM Ident Int -> ClassAssert -> TypePred
> toTypePred'' tvs (ClassAssert cls tv) =
>   TypePred cls (toType'' tvs (VariableType tv))

> toType'' :: FM Ident Int -> TypeExpr -> Type
> toType'' tvs ty = toTypeApp tvs ty []

> toTypeApp :: FM Ident Int -> TypeExpr -> [Type] -> Type
> toTypeApp tvs (ConstructorType tc) tys
>   | tc == qArrowId && length tys == 2 = TypeArrow (tys !! 0) (tys !! 1)
>   | otherwise = foldl TypeApply (TypeConstructor tc) tys
> toTypeApp tvs (VariableType tv) tys =
>   maybe (internalError ("toType " ++ show tv))
>         (\tv -> foldl TypeApply (TypeVariable tv) tys)
>         (lookupFM tv tvs)
> toTypeApp tvs (TupleType tys) tys'
>   | null tys' = tupleType (map (toType'' tvs) tys)
>   | otherwise = internalError "toType (TupleType)"
> toTypeApp tvs (ListType ty) tys
>   | null tys = listType (toType'' tvs ty)
>   | otherwise = internalError "toType (ListType)"
> toTypeApp tvs (ArrowType ty1 ty2) tys
>   | null tys = TypeArrow (toType'' tvs ty1) (toType'' tvs ty2)
>   | otherwise = internalError "toType (ArrowType)"
> toTypeApp tvs (ApplyType ty1 ty2) tys =
>   toTypeApp tvs ty1 (toType'' tvs ty2 : tys)

> qualifyQualType :: ModuleIdent -> QualType -> QualType
> qualifyQualType m (QualType cx ty) =
>   QualType (map (qualifyTypePred m) cx) (qualifyType m ty)

> qualifyTypePred :: ModuleIdent -> TypePred -> TypePred
> qualifyTypePred m (TypePred cls ty) =
>   TypePred (qualQualify m cls) (qualifyType m ty)

> qualifyType :: ModuleIdent -> Type -> Type
> qualifyType m (TypeConstructor tc) =
>   TypeConstructor (if isPrimTypeId tc then tc else qualQualify m tc)
> qualifyType _ (TypeVariable tv) = TypeVariable tv
> qualifyType m (TypeConstrained tys tv) =
>   TypeConstrained (map (qualifyType m) tys) tv
> qualifyType _ (TypeSkolem k) = TypeSkolem k
> qualifyType m (TypeApply ty1 ty2) =
>   TypeApply (qualifyType m ty1) (qualifyType m ty2)
> qualifyType m (TypeArrow ty1 ty2) =
>   TypeArrow (qualifyType m ty1) (qualifyType m ty2)

\end{verbatim}
The functions \texttt{fromType} and \texttt{fromQualType} convert a
(qualified) type into a (qualified) Curry type expression. During the
conversion, the compiler removes unnecessary module qualifiers from
all type constructors and type classes that are in scope with
unqualified names.
\begin{verbatim}

> fromType :: TCEnv -> Type -> TypeExpr
> fromType tcEnv ty = fromType' (unqualifyType tcEnv ty)

> fromQualType :: TCEnv -> QualType -> QualTypeExpr
> fromQualType tcEnv ty = fromQualType' (unqualifyQualType tcEnv ty)

> fromQualType' :: QualType -> QualTypeExpr
> fromQualType' (QualType cx ty) =
>   QualTypeExpr (map fromTypePred' cx) (fromType' ty)

> fromTypePred' :: TypePred -> ClassAssert
> fromTypePred' (TypePred cls ty) =
>   case fromType' ty of
>     VariableType tv -> ClassAssert cls tv
>     _ -> internalError ("fromTypePred " ++ show ty)

> fromType' :: Type -> TypeExpr
> fromType' ty = fromTypeApp ty []

> fromTypeApp :: Type -> [TypeExpr] -> TypeExpr
> fromTypeApp (TypeConstructor tc) tys
>   | isQTupleId tc && length tys == qTupleArity tc = TupleType tys
>   | tc == qListId && length tys == 1 = ListType (head tys)
>   | otherwise = foldl ApplyType (ConstructorType tc) tys
> fromTypeApp (TypeVariable tv) tys =
>   foldl ApplyType
>         (VariableType (if tv >= 0 then nameSupply !! tv
>                                   else mkIdent ('_' : show (-tv))))
>         tys
> fromTypeApp (TypeConstrained tys _) tys' = fromTypeApp (head tys) tys'
> fromTypeApp (TypeSkolem k) tys =
>   foldl ApplyType (VariableType (mkIdent ("_?" ++ show k))) tys
> fromTypeApp (TypeApply ty1 ty2) tys = fromTypeApp ty1 (fromType' ty2 : tys)
> fromTypeApp (TypeArrow ty1 ty2) tys =
>   foldl ApplyType (ArrowType (fromType' ty1) (fromType' ty2)) tys

> unqualifyQualType :: TCEnv -> QualType -> QualType
> unqualifyQualType tcEnv (QualType cx ty) =
>   QualType (map (unqualifyTypePred tcEnv) cx) (unqualifyType tcEnv ty)

> unqualifyTypePred :: TCEnv -> TypePred -> TypePred
> unqualifyTypePred tcEnv (TypePred cls ty) =
>   TypePred (unqualifyTC tcEnv cls) (unqualifyType tcEnv ty)

> unqualifyType :: TCEnv -> Type -> Type
> unqualifyType tcEnv (TypeConstructor tc) =
>   TypeConstructor (unqualifyTC tcEnv tc)
> unqualifyType _ (TypeVariable tv) = TypeVariable tv
> unqualifyType tcEnv (TypeConstrained tys tv) =
>   TypeConstrained (map (unqualifyType tcEnv) tys) tv
> unqualifyType _ (TypeSkolem k) = TypeSkolem k
> unqualifyType tcEnv (TypeApply ty1 ty2) =
>   TypeApply (unqualifyType tcEnv ty1) (unqualifyType tcEnv ty2)
> unqualifyType tcEnv (TypeArrow ty1 ty2) =
>   TypeArrow (unqualifyType tcEnv ty1) (unqualifyType tcEnv ty2)

> unqualifyTC :: TCEnv -> QualIdent -> QualIdent
> unqualifyTC tcEnv tc =
>   case lookupTopEnv tc' tcEnv of
>     [t] | origName t == tc -> qualify tc'
>     _ -> tc
>   where tc' = unqualify tc

\end{verbatim}
The functions \texttt{expandMonoType} and \texttt{expandPolyType}
convert (qualified) type expressions into (qualified) types and also
expand all type synonyms and qualify all type constructors during the
conversion. In contrast to \texttt{toType}, \texttt{toTypes}, and
\texttt{toQualType} above, which simply add the given module qualifier
to all unqualified type constructor and type class identifiers,
\texttt{expandMonoType} and \texttt{expandPolyType} look up the
correct module qualifiers in the type constructor environment.

The function \texttt{expandConstrType} computes the type of a data or
newtype constructor from the context, type name, and type variables
from the left hand side of the type declaration and the constructor's
argument types. Similar to \texttt{toConstrType}, the type's context
is restricted to those type variables which are free in the argument
types. However, type synonyms are expanded and type constructors and
type classes are qualified with the name of the module containing their
definition.

The function \texttt{expandMethodType} converts the type of a type
class method. Similar to function \texttt{toMethodType}, the implicit
type class constraint is added to the method's type and the class'
type variable is assigned index 0. However, type synonyms are expanded
and type constructors and type classes are qualified with the name of
the module containing their definition.
\begin{verbatim}

> expandMonoType :: TCEnv -> [Ident] -> TypeExpr -> Type
> expandMonoType tcEnv tvs ty = expandType tcEnv (toType' tvs ty)

> expandConstrType :: TCEnv -> [ClassAssert] -> QualIdent -> [Ident]
>                  -> [TypeExpr] -> QualType
> expandConstrType tcEnv cx tc tvs tys =
>   normalize (length tvs) (expandQualType tcEnv (toConstrType' cx tc tvs tys))

> expandMethodType :: TCEnv -> QualIdent -> Ident -> QualTypeExpr -> QualType
> expandMethodType tcEnv cls tv ty =
>   normalize 1 (expandQualType tcEnv (toMethodType' cls tv ty))

> expandPolyType :: TCEnv -> QualTypeExpr -> QualType
> expandPolyType tcEnv ty = normalize 0 (expandQualType tcEnv (toQualType' ty))

> expandQualType :: TCEnv -> QualType -> QualType
> expandQualType tcEnv (QualType cx ty) =
>   QualType (expandContext tcEnv cx) (expandType tcEnv ty)

> expandContext :: TCEnv -> [TypePred] -> [TypePred]
> expandContext tcEnv cx = minContext tcEnv (map (expandTypePred tcEnv) cx)

> expandTypePred :: TCEnv -> TypePred -> TypePred
> expandTypePred tcEnv (TypePred cls ty) =
>   TypePred (origName (head (qualLookupTopEnv cls tcEnv)))
>            (expandType tcEnv ty)

> expandType :: TCEnv -> Type -> Type
> expandType tcEnv ty = expandTypeApp tcEnv ty []

> expandTypeApp :: TCEnv -> Type -> [Type] -> Type
> expandTypeApp tcEnv (TypeConstructor tc) tys =
>   case qualLookupTopEnv tc tcEnv of
>     [DataType tc' _ _] -> foldl TypeApply (TypeConstructor tc') tys
>     [RenamingType tc' _ _] -> foldl TypeApply (TypeConstructor tc') tys
>     [AliasType _ _ ty] -> expandAliasType tys ty
>     _ -> internalError ("expandType " ++ show tc)
> expandTypeApp _ (TypeVariable tv) tys = foldl TypeApply (TypeVariable tv) tys
> expandTypeApp _ (TypeConstrained tys tv) tys' =
>   foldl TypeApply (TypeConstrained tys tv) tys'
> expandTypeApp _ (TypeSkolem k) tys = foldl TypeApply (TypeSkolem k) tys
> expandTypeApp tcEnv (TypeApply ty1 ty2) tys =
>   expandTypeApp tcEnv ty1 (expandType tcEnv ty2 : tys)
> expandTypeApp tcEnv (TypeArrow ty1 ty2) tys =
>   foldl TypeApply
>         (TypeArrow (expandType tcEnv ty1) (expandType tcEnv ty2))
>         tys

\end{verbatim}
The function \texttt{minContext} transforms a context by removing all
type predicates from the context which are implied by other predicates
according to the super class hierarchy. Inversely, the function
\texttt{maxContext} adds all predicates to a context which are implied
by the predicates in the given context.
\begin{verbatim}

> minContext :: TCEnv -> Context -> Context
> minContext tcEnv cx = cx' \\ concatMap implied cx'
>   where cx' = nub cx
>         implied (TypePred cls ty) =
>           [TypePred cls' ty | cls' <- tail (allSuperClasses cls tcEnv)]

> maxContext :: TCEnv -> Context -> Context
> maxContext tcEnv cx = nub (concatMap implied cx)
>   where implied (TypePred cls ty) =
>           [TypePred cls' ty | cls' <- sort (allSuperClasses cls tcEnv)]

\end{verbatim}
The following functions implement pretty-printing for types by
converting them into type expressions.
\begin{verbatim}

> ppType :: TCEnv -> Type -> Doc
> ppType tcEnv = ppTypeExpr 0 . fromType tcEnv

> ppQualType :: TCEnv -> QualType -> Doc
> ppQualType tcEnv = ppQualTypeExpr . fromQualType tcEnv

> ppTypeScheme :: TCEnv -> TypeScheme -> Doc
> ppTypeScheme tcEnv (ForAll _ ty) = ppQualType tcEnv ty

\end{verbatim}
