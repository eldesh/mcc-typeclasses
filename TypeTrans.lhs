% -*- LaTeX -*-
% $Id: TypeTrans.lhs 3322 2020-01-12 14:45:55Z wlux $
%
% Copyright (c) 1999-2020, Wolfgang Lux
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
>                  ppType, ppQualType, ppTypeScheme, ppInstance) where
> import Base
> import Curry
> import CurryPP
> import List
> import Map
> import PredefIdent
> import PredefTypes
> import Pretty
> import TopEnv
> import Types
> import TypeInfo
> import TypeSubst
> import ValueInfo

\end{verbatim}
The functions \texttt{toType} and \texttt{toTypes} convert Curry type
expressions into types. The function \texttt{toQualType} similarly
converts a qualified type expression into a qualified type.

The function \texttt{toConstrType} returns the type and additional
information for a data or newtype constructor. A special feature of
this function is that it restricts the context on the left hand side
of the type declaration to those constraints that affect the free type
variables from the argument types, as specified in Sect.~4.2.1 of the
revised Haskell'98 report~\cite{PeytonJones03:Haskell}. Type
constraints from a right hand context are not pruned because they
introduce additional local instances for the scope of a pattern. For
instance, consider an implementation of sets based on ordered binary
trees that incorporate their ordering relation:
\begin{verbatim}
  data Set a = Ord a => Empty | Ord a => Elem (Set a) a (Set a)
  add x t@Empty = Elem t x t
  add x (Elem l y r) =
    case compare x y of
      LT -> Elem (add x l) y r
      EQ -> Elem l y r
      GT -> Elem l y (add x r)
\end{verbatim}
Without the \texttt{Ord a} constraint for the \texttt{Empty}
constructor, the \texttt{Ord} instance required by the \texttt{Elem}
expression in the body of the first equation would have to be supplied
to this function. Note that the as-pattern is necessary to tell the
compiler that the \texttt{Elem} expression on the right hand side
belongs to the same \texttt{Set} type as the \texttt{Empty} pattern on
the left hand side.

The function \texttt{toMethodType} returns the type of a type class
method. It adds the implicit type class constraint to the method's
type signature and ensures that the class' type variable is always
assigned index 0.

Type variables are assigned ascending indices in the order of their
occurrence in the types. It is possible to pass a list of additional
type variables to these functions, which are assigned indices before
those variables occurring in the type. This allows preserving the
order of type variables in the left hand side of a type declaration
and in the head of a type class declaration, respectively.

Note the subtle difference between \texttt{toTypes tvs tys} and
\texttt{map (toType tvs) tys}. The former ensures that consistent
indices are assigned to all type variables occurring in the type
expressions \texttt{tys}, whereas the latter assigns type variable
indices independently in each type expression.
\begin{verbatim}

> toType :: [Ident] -> TypeExpr -> Type
> toType tvs ty = toType' (enumTypeVars tvs ty) ty

> toTypes :: [Ident] -> [TypeExpr] -> [Type]
> toTypes tvs tys = map (toType' (enumTypeVars tvs tys)) tys

> toQualType :: QualTypeExpr -> QualType
> toQualType ty = toQualType' (enumTypeVars [] ty) ty

> toConstrType :: [ClassAssert] -> QualIdent -> [Ident] -> [ClassAssert]
>              -> [TypeExpr] -> (ConstrInfo,QualType)
> toConstrType cxL tc tvs cxR tys =
>   (ConstrInfo (length (filter (`notElem` tvs) tvs'')) (toContext' tvs' cxR),
>    canonType (toQualType' tvs' (QualTypeExpr (cxL' ++ cxR) ty')))
>   where tvs' = enumTypeVars tvs tys
>         tvs'' = nub (fv tys)
>         cxL' = restrictContext tvs'' cxL
>         ty' = foldr ArrowType ty0 tys
>         ty0 = foldl ApplyType (ConstructorType tc) (map VariableType tvs)

> toMethodType :: QualIdent -> Ident -> QualTypeExpr -> QualType
> toMethodType cls tv (QualTypeExpr cx ty) =
>   toQualType' tvs (QualTypeExpr (ClassAssert cls (VariableType tv) : cx) ty)
>   where tvs = enumTypeVars [tv] (QualTypeExpr cx ty)

> enumTypeVars :: Expr a => [Ident] -> a -> FM Ident Int
> enumTypeVars tvs ty = fromListFM (zip (tvs ++ tvs') [0..])
>   where tvs' = [tv | tv <- nub (fv ty), tv `notElem` tvs]

> restrictContext :: [Ident] -> [ClassAssert] -> [ClassAssert]
> restrictContext tvs cx =
>   [ClassAssert cls ty | ClassAssert cls ty <- cx, cvar ty `elem` tvs]
>   where cvar (VariableType tv) = tv
>         cvar (ApplyType ty _) = cvar ty

> toQualType' :: FM Ident Int -> QualTypeExpr -> QualType
> toQualType' tvs (QualTypeExpr cx ty) =
>   QualType (toContext' tvs cx) (toType' tvs ty)

> toContext' :: FM Ident Int -> [ClassAssert] -> Context
> toContext' tvs cx = nub (map (toTypePred' tvs) cx)

> toTypePred' :: FM Ident Int -> ClassAssert -> TypePred
> toTypePred' tvs (ClassAssert cls ty) = TypePred cls (toType' tvs ty)

> toType' :: FM Ident Int -> TypeExpr -> Type
> toType' tvs ty = toTypeApp tvs ty []

> toTypeApp :: FM Ident Int -> TypeExpr -> [Type] -> Type
> toTypeApp tvs (ConstructorType tc) tys
>   | unqualify tc == arrowId && length tys == 2 =
>       TypeArrow (tys !! 0) (tys !! 1)
>   | otherwise = foldl TypeApply (TypeConstructor tc) tys
> toTypeApp tvs (VariableType tv) tys =
>   maybe (internalError ("toType " ++ show tv))
>         (\tv -> foldl TypeApply (TypeVariable tv) tys)
>         (lookupFM tv tvs)
> toTypeApp tvs (TupleType tys) tys'
>   | null tys' = tupleType (map (toType' tvs) tys)
>   | otherwise = internalError "toType (TupleType)"
> toTypeApp tvs (ListType ty) tys
>   | null tys = listType (toType' tvs ty)
>   | otherwise = internalError "toType (ListType)"
> toTypeApp tvs (ArrowType ty1 ty2) tys
>   | null tys = TypeArrow (toType' tvs ty1) (toType' tvs ty2)
>   | otherwise = internalError "toType (ArrowType)"
> toTypeApp tvs (ApplyType ty1 ty2) tys =
>   toTypeApp tvs ty1 (toType' tvs ty2 : tys)

\end{verbatim}
The functions \texttt{fromType} and \texttt{fromQualType} convert a
(qualified) type into a (qualified) Curry type expression.
\begin{verbatim}

> fromType :: [Ident] -> Type -> TypeExpr
> fromType tvs ty = fromTypeApp tvs ty []

> fromQualType :: [Ident] -> QualType -> QualTypeExpr
> fromQualType tvs (QualType cx ty) =
>   QualTypeExpr (map (fromTypePred tvs) cx) (fromType tvs ty)

> fromTypePred :: [Ident] -> TypePred -> ClassAssert
> fromTypePred tvs (TypePred cls ty) = ClassAssert cls (fromType tvs ty)

> fromTypeApp :: [Ident] -> Type -> [TypeExpr] -> TypeExpr
> fromTypeApp _ (TypeConstructor tc) tys
>   | tc' == listId && length tys == 1 = ListType (head tys)
>   | isTupleId tc' && length tys == tupleArity tc' = TupleType tys
>   | otherwise = foldl ApplyType (ConstructorType tc) tys
>   where tc' = unqualify tc
> fromTypeApp tvs (TypeVariable tv) tys =
>   foldl ApplyType
>         (VariableType (if tv >= 0 then tvs !! tv
>                                   else mkIdent ('_' : show (-tv))))
>         tys
> fromTypeApp tvs (TypeConstrained tys _) tys' = fromTypeApp tvs (head tys) tys'
> fromTypeApp _ (TypeSkolem k) tys =
>   foldl ApplyType (VariableType (mkIdent ("_?" ++ show k))) tys
> fromTypeApp tvs (TypeApply ty1 ty2) tys =
>   fromTypeApp tvs ty1 (fromType tvs ty2 : tys)
> fromTypeApp tvs (TypeArrow ty1 ty2) tys =
>   foldl ApplyType (ArrowType (fromType tvs ty1) (fromType tvs ty2)) tys

\end{verbatim}
The functions \texttt{expandMonoType} and \texttt{expandPolyType}
convert (qualified) type expressions into (qualified) types and also
expand all type synonyms and qualify all type constructors during the
conversion.

The function \texttt{expandConstrType} computes the type and
additional information for a data or newtype constructor. Similar to
\texttt{toConstrType}, the type's left hand side context is restricted
to those type constraints that apply to the free variables of the
argument types. However, type synonyms are expanded and type
constructors and type classes are qualified with the name of the
module containing their definition.

The function \texttt{expandMethodType} converts the type of a type
class method. Similar to function \texttt{toMethodType}, the implicit
type class constraint is added to the method's type and the class'
type variable is assigned index 0. However, type synonyms are expanded
and type constructors and type classes are qualified with the name of
the module containing their definition.
\begin{verbatim}

> expandMonoType :: TCEnv -> [Ident] -> TypeExpr -> Type
> expandMonoType tcEnv tvs = expandType tcEnv . toType tvs

> expandConstrType :: TCEnv -> [ClassAssert] -> QualIdent -> [Ident]
>                  -> [ClassAssert] -> [TypeExpr] -> (ConstrInfo,QualType)
> expandConstrType tcEnv cxL tc tvs cxR tys =
>   (ConstrInfo n' cxR'',normalize n (expandQualType tcEnv ty'))
>   where n = length tvs
>         (ConstrInfo n' cxR',ty') = toConstrType cxL tc tvs cxR tys
>         QualType cxR'' _ =
>           normalize n (expandQualType tcEnv (contextMap (const cxR') ty'))

> expandMethodType :: TCEnv -> QualIdent -> Ident -> QualTypeExpr -> QualType
> expandMethodType tcEnv cls tv =
>   normalize 1 . expandQualType tcEnv . toMethodType cls tv

> expandPolyType :: TCEnv -> QualTypeExpr -> QualType
> expandPolyType tcEnv = normalize 0 . expandQualType tcEnv . toQualType

> expandQualType :: TCEnv -> QualType -> QualType
> expandQualType tcEnv (QualType cx ty) =
>   QualType (expandContext tcEnv cx) (expandType tcEnv ty)

> expandContext :: TCEnv -> [TypePred] -> [TypePred]
> expandContext tcEnv cx = minContext tcEnv (map (expandTypePred tcEnv) cx)

> expandTypePred :: TCEnv -> TypePred -> TypePred
> expandTypePred tcEnv (TypePred cls ty) =
>   case qualLookupTopEnv cls tcEnv of
>     [TypeClass cls' _ _ _] -> TypePred cls' (expandType tcEnv ty)
>     _ -> internalError ("expandTypePred " ++ show cls)

> expandType :: TCEnv -> Type -> Type
> expandType tcEnv ty = expandTypeApp tcEnv ty []

> expandTypeApp :: TCEnv -> Type -> [Type] -> Type
> expandTypeApp tcEnv (TypeConstructor tc) tys =
>   case qualLookupTopEnv tc tcEnv of
>     [DataType tc' _ _] -> foldl TypeApply (TypeConstructor tc') tys
>     [RenamingType tc' _ _] -> foldl TypeApply (TypeConstructor tc') tys
>     [AliasType _ n _ ty] -> applyType (instTypeScheme tys' ty) tys''
>       where (tys',tys'') = splitAt n tys
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
converting them into type expressions. In order to improve
readability, module qualifiers are removed as far as possible.
\begin{verbatim}

> ppType :: TCEnv -> Type -> Doc
> ppType tcEnv = ppTypeExpr 0 . fromType nameSupply . unqualifyType tcEnv

> ppQualType :: TCEnv -> QualType -> Doc
> ppQualType tcEnv =
>   ppQualTypeExpr . fromQualType nameSupply . unqualifyQualType tcEnv

> ppTypeScheme :: TCEnv -> TypeScheme -> Doc
> ppTypeScheme tcEnv (ForAll _ ty) = ppQualType tcEnv ty

> ppInstance :: TCEnv -> TypePred -> Doc
> ppInstance tcEnv =
>   ppClassAssert . fromTypePred nameSupply . unqualifyTypePred tcEnv

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

> unqualifyQualType :: TCEnv -> QualType -> QualType
> unqualifyQualType tcEnv (QualType cx ty) =
>   QualType (map (unqualifyTypePred tcEnv) cx) (unqualifyType tcEnv ty)

> unqualifyTypePred :: TCEnv -> TypePred -> TypePred
> unqualifyTypePred tcEnv (TypePred cls ty) =
>   TypePred (unqualifyTC tcEnv cls) (unqualifyType tcEnv ty)

> unqualifyTC :: TCEnv -> QualIdent -> QualIdent
> unqualifyTC tcEnv tc
>   | isPrimTypeId tc' = qualify tc'
>   | otherwise =
>       case lookupTopEnv tc' tcEnv of
>         [t] | origName t == tc -> qualify tc'
>         _ -> tc
>   where tc' = unqualify tc

\end{verbatim}
