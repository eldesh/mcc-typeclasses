% -*- LaTeX -*-
% $Id: TypeSubst.lhs 3242 2016-06-19 10:53:21Z wlux $
%
% Copyright (c) 2003-2015, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{TypeSubst.lhs}
\section{Type Substitutions}
This module implements substitutions on types.
\begin{verbatim}

> module TypeSubst(TypeSubst, SubstType(..), bindVar, substVar,
>                  InstTypeScheme(..), normalize, instanceType,
>                  idSubst, bindSubst, compose) where
> import List
> import Maybe
> import Subst
> import TopEnv
> import Types
> import ValueInfo

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
>   subst _ (DataConstructor c ls ci ty) = DataConstructor c ls ci ty
>   subst _ (NewtypeConstructor c l ty) = NewtypeConstructor c l ty
>   subst sigma (Value v n ty) = Value v n (subst sigma ty)

> instance SubstType a => SubstType (TopEnv a) where
>   subst = fmap . subst

\end{verbatim}
The class method \texttt{instTypeScheme} instantiates a type scheme by
substituting the given types for the universally quantified type
variables in a type (scheme). After a substitution the compiler must
recompute the type indices for all type variables. Otherwise,
expanding a type synonym like \verb|type Pair' a b = (b,a)| could
break the invariant that the universally quantified type variables are
assigned indices in the order of their occurrence. This is handled by
function \texttt{normalize}. The function has a threshold parameter
that allows preserving the indices of type variables bound on the left
hand side of a type declaration and in the head of a type class
declaration, respectively.
\begin{verbatim}

> class InstTypeScheme t where
>   instTypeScheme :: [Type] -> t -> t

> instance InstTypeScheme Type where
>   instTypeScheme tys ty = instTypeApp tys ty []

> instTypeApp :: [Type] -> Type -> [Type] -> Type
> instTypeApp _ (TypeConstructor tc) = foldl TypeApply (TypeConstructor tc)
> instTypeApp tys (TypeVariable n)
>   | n >= 0 = applyType (tys !! n)
>   | otherwise = foldl TypeApply (TypeVariable n)
> instTypeApp _ (TypeConstrained tys n) =
>   foldl TypeApply (TypeConstrained tys n)
> instTypeApp _ (TypeSkolem k) = foldl TypeApply (TypeSkolem k)
> instTypeApp tys (TypeApply ty1 ty2) =
>   instTypeApp tys ty1 . (instTypeScheme tys ty2 :)
> instTypeApp tys (TypeArrow ty1 ty2) =
>   foldl TypeApply
>         (TypeArrow (instTypeScheme tys ty1) (instTypeScheme tys ty2))

> instance InstTypeScheme TypePred where
>   instTypeScheme tys (TypePred cls ty) = TypePred cls (instTypeScheme tys ty)

> instance InstTypeScheme QualType where
>   instTypeScheme tys (QualType cx ty) =
>     QualType (map (instTypeScheme tys) cx) (instTypeScheme tys ty)

> normalize :: Int -> QualType -> QualType
> normalize n ty =
>   canonType (instTypeScheme [TypeVariable (occur tv) | tv <- [0..]] ty)
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

> instanceType :: InstTypeScheme a => Type -> a -> a
> instanceType ty = instTypeScheme (ty : map TypeVariable [n..])
>   where ForAll n _ = polyType ty

\end{verbatim}
