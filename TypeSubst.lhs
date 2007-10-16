% -*- LaTeX -*-
% $Id: TypeSubst.lhs 2500 2007-10-16 19:41:32Z wlux $
%
% Copyright (c) 2003-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{TypeSubst.lhs}
\section{Type Substitutions}
This module implements substitutions on types.
\begin{verbatim}

> module TypeSubst(TypeSubst, SubstType(..), bindVar, substVar,
>                  ExpandAliasType(..), normalize, instanceType,
>                  idSubst, bindSubst, compose) where
> import Base
> import List
> import Maybe
> import Subst
> import TopEnv
> import Types

> type TypeSubst = Subst Int Type

> class SubstType a where
>   subst :: TypeSubst -> a -> a

> bindVar :: Int -> Type -> TypeSubst -> TypeSubst
> bindVar tv ty = compose (bindSubst tv ty idSubst)

> substVar :: TypeSubst -> Int -> Type
> substVar = substVar' TypeVariable subst

> instance SubstType a => SubstType [a] where
>   subst sigma = map (subst sigma)

> instance SubstType Type where
>   subst sigma ty = substTypeApp sigma ty []

> substTypeApp :: TypeSubst -> Type -> [Type] -> Type
> substTypeApp _ (TypeConstructor tc) = foldl TypeApply (TypeConstructor tc)
> substTypeApp sigma (TypeVariable tv) = applyType (substVar sigma tv)
> substTypeApp sigma (TypeConstrained tys tv) =
>   case substVar sigma tv of
>     TypeVariable tv -> foldl TypeApply (TypeConstrained tys tv)
>     ty -> foldl TypeApply ty
> substTypeApp _ (TypeSkolem k) = foldl TypeApply (TypeSkolem k)
> substTypeApp sigma (TypeApply ty1 ty2) =
>   substTypeApp sigma ty1 . (subst sigma ty2 :)
> substTypeApp sigma (TypeArrow ty1 ty2) =
>   foldl TypeApply (TypeArrow (subst sigma ty1) (subst sigma ty2))

> instance SubstType TypePred where
>   subst sigma (TypePred cls ty) = TypePred cls (subst sigma ty)

> instance SubstType QualType where
>   subst sigma (QualType cx ty) = QualType (subst sigma cx) (subst sigma ty)

> instance SubstType TypeScheme where
>   subst sigma (ForAll n ty) = ForAll n (subst sigma' ty)
>     where sigma' = foldr unbindSubst sigma [0..n-1]

> instance SubstType ValueInfo where
>   subst _ (DataConstructor c n ci ty) = DataConstructor c n ci ty
>   subst _ (NewtypeConstructor c ty) = NewtypeConstructor c ty
>   subst sigma (Value v n ty) = Value v n (subst sigma ty)

> instance SubstType a => SubstType (TopEnv a) where
>   subst = fmap . subst

\end{verbatim}
The class method \texttt{expandAliasType} expands all occurrences of a
type synonym in its (second) argument. After the expansion we have to
reassign the type indices of all type variables. Otherwise, expanding
a type synonym like \verb|type Pair' a b = (b,a)| could break the
invariant that the universally quantified type variables are assigned
indices in the order of their occurrence. This is handled by function
\texttt{normalize}. The function has a threshold parameter that allows
preserving the indices of type variables bound on the left hand side
of a type declaration and in the head of a type class declaration,
respectively.
\begin{verbatim}

> class ExpandAliasType t where
>   expandAliasType :: [Type] -> t -> t

> instance ExpandAliasType Type where
>   expandAliasType tys ty = expandTypeApp tys ty []

> expandTypeApp :: [Type] -> Type -> [Type] -> Type
> expandTypeApp _ (TypeConstructor tc) = foldl TypeApply (TypeConstructor tc)
> expandTypeApp tys (TypeVariable n)
>   | n >= 0 = applyType (tys !! n)
>   | otherwise = foldl TypeApply (TypeVariable n)
> expandTypeApp _ (TypeConstrained tys n) =
>   foldl TypeApply (TypeConstrained tys n)
> expandTypeApp _ (TypeSkolem k) = foldl TypeApply (TypeSkolem k)
> expandTypeApp tys (TypeApply ty1 ty2) =
>   expandTypeApp tys ty1 . (expandAliasType tys ty2 :)
> expandTypeApp tys (TypeArrow ty1 ty2) =
>   foldl TypeApply
>         (TypeArrow (expandAliasType tys ty1) (expandAliasType tys ty2))

> instance ExpandAliasType TypePred where
>   expandAliasType tys (TypePred cls ty) =
>     TypePred cls (expandAliasType tys ty)

> instance ExpandAliasType QualType where
>   expandAliasType tys (QualType cx ty) =
>     QualType (map (expandAliasType tys) cx) (expandAliasType tys ty)

> normalize :: Int -> QualType -> QualType
> normalize n ty =
>   canonType (expandAliasType [TypeVariable (occur tv) | tv <- [0..]] ty)
>   where tvs' = zip (nub (filter (>= n) (typeVars ty))) [n..]
>         occur tv = fromMaybe tv (lookup tv tvs')

\end{verbatim}
The function \texttt{instanceType} computes an instance of a
polymorphic type by substituting the first type argument for all
occurrences of the type variable with index 0 in the second argument.
The function carefully assigns new indices to all other type variables
of the second argument so that they do not conflict with the type
variables of the first argument.
\begin{verbatim}

> instanceType :: ExpandAliasType a => Type -> a -> a
> instanceType ty = expandAliasType (ty : map TypeVariable [n..])
>   where ForAll n _ = polyType ty

\end{verbatim}
