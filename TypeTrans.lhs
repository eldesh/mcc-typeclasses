% -*- LaTeX -*-
% $Id: TypeTrans.lhs 2071 2007-01-15 22:21:22Z wlux $
%
% Copyright (c) 1999-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{TypeTrans.lhs}
\section{Type Transformations}
This module implements transformations between the internal and
external type representations.
\begin{verbatim}

> module TypeTrans(toType, toTypes, toQualType, toConstrType, toTypeScheme,
>                  fromType, fromQualType,
>                  expandMonoType, expandConstrType, expandPolyType,
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
into a qualified type and a type scheme, respectively. The function
\texttt{toConstrType} returns the type of a data or newtype
constructor. It computes the constructor's type from the context, type
name, and type variables from the left hand side of the type
declaration and the constructor's argument types. A special feature of
this function is that it restricts the context to those type variables
which are free in the argument types as specified in Sect.~4.2.1 of
the revised Haskell'98 report~\cite{PeytonJones03:Haskell}.

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
> toType m tvs ty = qualifyType m (toType' (enumTypeVars tvs ty) ty)

> toTypes :: ModuleIdent -> [Ident] -> [TypeExpr] -> [Type]
> toTypes m tvs tys = map (qualifyType m . toType' (enumTypeVars tvs tys)) tys

> toQualType :: ModuleIdent -> [Ident] -> QualTypeExpr -> QualType
> toQualType m tvs ty = qualifyQualType m (toQualType' (enumTypeVars tvs ty) ty)

> toConstrType :: ModuleIdent -> [ClassAssert] -> QualIdent -> [Ident]
>              -> [TypeExpr] -> QualType
> toConstrType m cx tc tvs tys = toQualType m tvs (QualTypeExpr cx' ty')
>   where cx' = restrictContext tys cx
>         ty' = foldr ArrowType (ConstructorType tc (map VariableType tvs)) tys

> toTypeScheme :: ModuleIdent -> QualTypeExpr -> TypeScheme
> toTypeScheme m ty = typeScheme (toQualType m [] ty)

> enumTypeVars :: Expr a => [Ident] -> a -> FM Ident Int
> enumTypeVars tvs ty = fromListFM (zip (tvs ++ tvs') [0..])
>   where tvs' = [tv | tv <- nub (fv ty), tv `notElem` tvs]

> restrictContext :: [TypeExpr] -> [ClassAssert] -> [ClassAssert]
> restrictContext tys cx =
>   [ClassAssert cls tv | ClassAssert cls tv <- cx, tv `elem` tvs'']
>   where tvs'' = nub (fv tys)

> toQualType' :: FM Ident Int -> QualTypeExpr -> QualType
> toQualType' tvs (QualTypeExpr cx ty) =
>   QualType (nub (map (toTypePred' tvs) cx)) (toType' tvs ty)

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
> fromType' (TypeConstructor tc tys)
>   | isQTupleId tc = TupleType tys'
>   | tc == qListId && length tys == 1 = ListType (head tys')
>   | otherwise = ConstructorType tc tys'
>   where tys' = map fromType' tys
> fromType' (TypeVariable tv) =
>   VariableType (if tv >= 0 then nameSupply !! tv
>                            else mkIdent ('_' : show (-tv)))
> fromType' (TypeConstrained tys _) = fromType' (head tys)
> fromType' (TypeArrow ty1 ty2) = ArrowType (fromType' ty1) (fromType' ty2)
> fromType' (TypeSkolem k) = VariableType (mkIdent ("_?" ++ show k))

> unqualifyQualType :: TCEnv -> QualType -> QualType
> unqualifyQualType tcEnv (QualType cx ty) =
>   QualType (map (unqualifyTypePred tcEnv) cx) (unqualifyType tcEnv ty)

> unqualifyTypePred :: TCEnv -> TypePred -> TypePred
> unqualifyTypePred tcEnv (TypePred cls ty) =
>   TypePred (unqualifyTC tcEnv cls) (unqualifyType tcEnv ty)

> unqualifyType :: TCEnv -> Type -> Type
> unqualifyType tcEnv (TypeConstructor tc tys) =
>   TypeConstructor (unqualifyTC tcEnv tc) (map (unqualifyType tcEnv) tys)
> unqualifyType _ (TypeVariable tv) = TypeVariable tv
> unqualifyType tcEnv (TypeConstrained tys tv) =
>   TypeConstrained (map (unqualifyType tcEnv) tys) tv
> unqualifyType tcEnv (TypeArrow ty1 ty2) =
>   TypeArrow (unqualifyType tcEnv ty1) (unqualifyType tcEnv ty2)
> unqualifyType _ (TypeSkolem k) = TypeSkolem k

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
conversion. Qualification and expansion have to be performed at the
same time since type constructors are recorded in the type constructor
environment using the names visible in the source code, but the
expanded types refer to the original names.

The function \texttt{expandConstrType} computes the type of a data or
newtype constructor from the context, type name, and type variables
from the left hand side of the type declaration and the constructor's
argument types. Similar to \texttt{toConstrType}, the type's context
is restricted to those type variables which are free in the argument
types.
\begin{verbatim}

> expandMonoType :: TCEnv -> [Ident] -> TypeExpr -> Type
> expandMonoType tcEnv tvs ty =
>   expandType tcEnv (toType' (enumTypeVars tvs ty) ty)

> expandConstrType :: TCEnv -> [ClassAssert] -> QualIdent -> [Ident]
>                  -> [TypeExpr] -> QualType
> expandConstrType tcEnv cx tc tvs tys = normalize (length tvs) $
>   expandQualType tcEnv $ toQualType' tvs' (QualTypeExpr cx' ty')
>   where tvs' = enumTypeVars tvs tys
>         cx' = restrictContext tys cx
>         ty' = foldr ArrowType (ConstructorType tc (map VariableType tvs)) tys

> expandPolyType :: TCEnv -> QualTypeExpr -> TypeScheme
> expandPolyType tcEnv ty =
>   typeScheme $ normalize 0 $ expandQualType tcEnv $ toQualType' tvs ty
>   where tvs = enumTypeVars [] ty

> expandQualType :: TCEnv -> QualType -> QualType
> expandQualType tcEnv (QualType cx ty) =
>   QualType (expandContext tcEnv cx) (expandType tcEnv ty)

> expandContext :: TCEnv -> [TypePred] -> [TypePred]
> expandContext tcEnv cx = impliedContext tcEnv (map (expandTypePred tcEnv) cx)

> expandTypePred :: TCEnv -> TypePred -> TypePred
> expandTypePred tcEnv (TypePred cls ty) = TypePred cls (expandType tcEnv ty)

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
The function \texttt{impliedContext} transforms a context by adding
type predicates for all type predicates which are implied by the super
class hierarchy.
\begin{verbatim}

> impliedContext :: TCEnv -> Context -> Context
> impliedContext tcEnv cx = nub (concatMap implied cx)
>   where implied (TypePred cls ty) =
>           case qualLookupTopEnv cls tcEnv of
>             [TypeClass cls' clss _] -> map (flip TypePred ty) (cls' : clss)
>             _ -> internalError ("implied " ++ show cls)

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
