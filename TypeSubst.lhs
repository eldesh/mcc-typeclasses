% -*- LaTeX -*-
% $Id: TypeSubst.lhs 2082 2007-01-24 20:11:46Z wlux $
%
% Copyright (c) 2003-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{TypeSubst.lhs}
\section{Type Substitutions}
This module implements substitutions on types.
\begin{verbatim}

> module TypeSubst(module TypeSubst, idSubst,bindSubst,compose) where
> import Base
> import TopEnv
> import Maybe
> import List
> import Subst

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
>   subst sigma (TypeConstructor tc tys) =
>     TypeConstructor tc (map (subst sigma) tys)
>   subst sigma (TypeVariable tv) = substVar sigma tv
>   subst sigma (TypeConstrained tys tv) =
>     case substVar sigma tv of
>       TypeVariable tv -> TypeConstrained tys tv
>       ty -> ty
>   subst sigma (TypeArrow ty1 ty2) =
>     TypeArrow (subst sigma ty1) (subst sigma ty2)
>   subst sigma (TypeSkolem k) = TypeSkolem k

> instance SubstType TypePred where
>   subst sigma (TypePred cls ty) = TypePred cls (subst sigma ty)

> instance SubstType QualType where
>   subst sigma (QualType cx ty) =
>     canonType (QualType (subst sigma cx) (subst sigma ty))

> instance SubstType TypeScheme where
>   subst sigma (ForAll n (QualType cx ty)) =
>     ForAll n (QualType cx (subst (foldr unbindSubst sigma [0..n-1]) ty))

> instance SubstType ValueInfo where
>   subst theta (DataConstructor c ty) = DataConstructor c ty
>   subst theta (NewtypeConstructor c ty) = NewtypeConstructor c ty
>   subst theta (Value v ty) = Value v (subst theta ty)

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
>   expandAliasType tys (TypeConstructor tc tys') =
>     TypeConstructor tc (map (expandAliasType tys) tys')
>   expandAliasType tys (TypeVariable n)
>     | n >= 0 = tys !! n
>     | otherwise = TypeVariable n
>   expandAliasType _ (TypeConstrained tys n) = TypeConstrained tys n
>   expandAliasType tys (TypeArrow ty1 ty2) =
>     TypeArrow (expandAliasType tys ty1) (expandAliasType tys ty2)
>   expandAliasType _ (TypeSkolem k) = TypeSkolem k

> instance ExpandAliasType TypePred where
>   expandAliasType tys (TypePred cls ty) =
>     TypePred cls (expandAliasType tys ty)

> instance ExpandAliasType QualType where
>   expandAliasType tys (QualType cx ty) =
>     canonType (QualType (map (expandAliasType tys) cx)
>                         (expandAliasType tys ty))

> normalize :: Int -> QualType -> QualType
> normalize n ty = expandAliasType [TypeVariable (occur tv) | tv <- [0..]] ty
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
