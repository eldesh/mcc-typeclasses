% -*- LaTeX -*-
% $Id: KindSubst.lhs 2513 2007-10-18 09:50:08Z wlux $
%
% Copyright (c) 2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{KindSubst.lhs}
\section{Kind Substitutions}
This module implements substitutions on kinds.
\begin{verbatim}

> module KindSubst(module KindSubst, idSubst,bindSubst,compose) where
> import Kinds
> import Subst
> import TopEnv
> import TypeInfo

> type KindSubst = Subst Int Kind

> class SubstKind a where
>   subst :: KindSubst -> a -> a

> bindVar :: Int -> Kind -> KindSubst -> KindSubst
> bindVar kv k = compose (bindSubst kv k idSubst)

> substVar :: KindSubst -> Int -> Kind
> substVar = substVar' KindVariable subst

> instance SubstKind Kind where
>   subst _ KindStar = KindStar
>   subst sigma (KindVariable kv) = substVar sigma kv
>   subst sigma (KindArrow k1 k2) = KindArrow (subst sigma k1) (subst sigma k2)

> instance SubstKind TypeInfo where
>   subst theta (DataType tc k cs) = DataType tc (subst theta k) cs
>   subst theta (RenamingType tc k nc) = RenamingType tc (subst theta k) nc
>   subst theta (AliasType tc n k ty) = AliasType tc n (subst theta k) ty
>   subst theta (TypeClass cls k clss fs) =
>     TypeClass cls (subst theta k) clss fs

> instance SubstKind a => SubstKind (TopEnv a) where
>   subst = fmap . subst

\end{verbatim}
