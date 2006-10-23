% -*- LaTeX -*-
% $Id: Typing.lhs 1979 2006-10-23 19:05:25Z wlux $
%
% Copyright (c) 2003-2006, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Typing.lhs}
\section{Computing the Type of Curry Expressions}
\begin{verbatim}

> module Typing(Typeable(..)) where
> import Base
> import TypeSubst
> import Combined
> import Monad
> import TopEnv
> import Utils

\end{verbatim}
During the transformation of Curry source code into the intermediate
language, the compiler has to recompute the types of expressions. This
is simpler than type checking because the types of all variables are
known. Yet, the compiler still must handle functions and constructors
with polymorphic types and instantiate their type schemes using fresh
type variables. Since all types computed by \texttt{typeOf} are
monomorphic, we can use type variables with non-negative offsets for
the instantiation of type schemes here without risk of name conflicts.
Using non-negative offsets also makes it easy to distinguish these
fresh variables from free type variables introduce during type
inference, which must be regarded as constants here.

However, using non-negative offsets for fresh type variables gives
rise to two problems when those types are entered back into the type
environment, e.g., while introducing auxiliary variables during
desugaring. The first is that those type variables now appear to be
universally quantified variables, but with indices greater than the
number of quantified type variables.\footnote{To be precise, this can
  happen only for auxiliary variables, which have monomorphic types,
  whereas auxiliary functions will be assigned polymorphic types and
  these type variables will be properly quantified. However, in this
  case the assigned types may be too general.} This results in an
internal error (``Prelude.!!: index too large'') whenever such a type
is instantiated. The second problem is that there may be inadvertent
name captures because \texttt{computeType} always uses indices
starting at 0 for the fresh type variables. In order to avoid these
problems, \texttt{computeType} renames all type variables with
non-negative offsets after the final type has been computed, using
negative indices below the one with the smallest value occurring in
the type environment. Computing the minimum index of all type
variables in the type environment seems prohibitively inefficient.
However, recall that, thanks to laziness, the minimum is computed only
when the final type contains any type variables with non-negative
indices. This happens, for instance, 36 times while compiling the
prelude (for 159 evaluated applications of \texttt{typeOf}) and only
twice while compiling the standard \texttt{IO} module (for 21
applications of \texttt{typeOf}).\footnote{These numbers were obtained
  for version 0.9.9.}

A careful reader will note that inadvertent name captures are still
possible if one computes the types of two or more auxiliary variables
before actually entering their types into the environment. Therefore,
make sure that you enter the types of these auxiliary variables
immediately into the type environment, unless you are sure that those
types cannot contain fresh type variables. One such case are the free
variables of a goal.

\ToDo{In the long run, this module should be made obsolete by adding
attributes to the abstract syntax tree -- e.g., along the lines of
Chap.~6 in~\cite{PeytonJonesLester92:Book} -- and returning an
abstract syntax tree attributed with type information together with
the type environment from type inference. This also would allow
getting rid of the identifiers in the representation of integer
literals, which are used in order to implement overloading of
integer constants.}

\ToDo{When computing the type of an expression with a type signature
make use of the annotation instead of recomputing its type. In order
to do this, we must either ensure that the types are properly
qualified and expanded or we need access to the type constructor
environment.}

\ToDo{Do not ignore contexts!}
\begin{verbatim}

> type TyState a = StateT TypeSubst (StateT Int Id) a

> run :: TyState a -> ValueEnv -> a
> run m tyEnv = runSt (callSt m idSubst) 0

> class Typeable a where
>   typeOf :: ValueEnv -> a -> Type

> instance Typeable Ident where
>   typeOf = computeType identType

> instance Typeable ConstrTerm where
>   typeOf = computeType argType

> instance Typeable Expression where
>   typeOf = computeType exprType

> instance Typeable Rhs where
>   typeOf = computeType rhsType

> computeType :: (ValueEnv -> a -> TyState Type) -> ValueEnv -> a -> Type
> computeType f tyEnv x = ty
>   where QualType _ ty = normalize 0 (qualType (run doComputeType tyEnv))
>         doComputeType =
>           do
>             ty <- f tyEnv x
>             theta <- fetchSt
>             return (fixTypeVars tyEnv (subst theta ty))

> fixTypeVars :: ValueEnv -> Type -> Type
> fixTypeVars tyEnv ty = subst (foldr2 bindSubst idSubst tvs tvs') ty
>   where tvs = filter (>= 0) (typeVars ty)
>         tvs' = map TypeVariable [n - 1,n - 2 ..]
>         n = minimum (0 : concatMap typeVars tys)
>         tys = [ty | (_,Value _ (ForAll _ ty)) <- localBindings tyEnv]

> identType :: ValueEnv -> Ident -> TyState Type
> identType tyEnv x = instUniv (varType x tyEnv)

> litType :: Literal -> Type
> litType (Char _) = charType
> litType (Int _) = intType
> litType (Float _) = floatType
> litType (String _) = stringType

> argType :: ValueEnv -> ConstrTerm -> TyState Type
> argType tyEnv (LiteralPattern l) = return (litType l)
> argType tyEnv (NegativePattern _ l) = return (litType l)
> argType tyEnv (VariablePattern v) = identType tyEnv v
> argType tyEnv (ConstructorPattern c ts) =
>   do
>     (tys,ty) <- liftM arrowUnapply (instUniv (conType c tyEnv))
>     tys' <- mapM (argType tyEnv) ts
>     unifyList tys tys'
>     return ty
> argType tyEnv (InfixPattern t1 op t2) =
>   argType tyEnv (ConstructorPattern op [t1,t2])
> argType tyEnv (ParenPattern t) = argType tyEnv t
> argType tyEnv (TuplePattern ts) = liftM tupleType (mapM (argType tyEnv) ts)
> argType tyEnv (ListPattern ts) =
>   do
>     ty <- freshTypeVar
>     mapM_ (elemType ty) ts
>     return (listType ty)
>   where elemType ty t = argType tyEnv t >>= unify ty
> argType tyEnv (AsPattern v _) = argType tyEnv (VariablePattern v)
> argType tyEnv (LazyPattern t) = argType tyEnv t

> exprType :: ValueEnv -> Expression -> TyState Type
> exprType tyEnv (Literal l) = return (litType l)
> exprType tyEnv (Variable v) = instUniv (funType v tyEnv)
> exprType tyEnv (Constructor c) = instUniv (conType c tyEnv)
> exprType tyEnv (Typed e _) = exprType tyEnv e
> exprType tyEnv (Paren e) = exprType tyEnv e
> exprType tyEnv (Tuple es) = liftM tupleType (mapM (exprType tyEnv) es)
> exprType tyEnv (List es) =
>   do
>     ty <- freshTypeVar
>     mapM_ (elemType ty) es
>     return (listType ty)
>   where elemType ty e = exprType tyEnv e >>= unify ty
> exprType tyEnv (ListCompr e _) = liftM listType (exprType tyEnv e)
> exprType tyEnv (EnumFrom _) = return (listType intType)
> exprType tyEnv (EnumFromThen _ _) = return (listType intType)
> exprType tyEnv (EnumFromTo _ _) = return (listType intType)
> exprType tyEnv (EnumFromThenTo _ _ _) = return (listType intType)
> exprType tyEnv (UnaryMinus _ e) = exprType tyEnv e
> exprType tyEnv (Apply e1 e2) =
>   do
>     (ty1,ty2) <- exprType tyEnv e1 >>= unifyArrow
>     exprType tyEnv e2 >>= unify ty1
>     return ty2
> exprType tyEnv (InfixApply e1 op e2) =
>   do
>     (ty1,ty2,ty3) <- exprType tyEnv (infixOp op) >>= unifyArrow2
>     exprType tyEnv e1 >>= unify ty1
>     exprType tyEnv e2 >>= unify ty2
>     return ty3
> exprType tyEnv (LeftSection e op) =
>   do
>     (ty1,ty2,ty3) <- exprType tyEnv (infixOp op) >>= unifyArrow2
>     exprType tyEnv e >>= unify ty1
>     return (TypeArrow ty2 ty3)
> exprType tyEnv (RightSection op e) =
>   do
>     (ty1,ty2,ty3) <- exprType tyEnv (infixOp op) >>= unifyArrow2
>     exprType tyEnv e >>= unify ty2
>     return (TypeArrow ty1 ty3)
> exprType tyEnv (Lambda args e) =
>   do
>     tys <- mapM (argType tyEnv) args
>     ty <- exprType tyEnv e
>     return (foldr TypeArrow ty tys)
> exprType tyEnv (Let _ e) = exprType tyEnv e
> exprType tyEnv (Do _ e) = exprType tyEnv e
> exprType tyEnv (IfThenElse e1 e2 e3) =
>   do
>     exprType tyEnv e1 >>= unify boolType
>     ty2 <- exprType tyEnv e2
>     ty3 <- exprType tyEnv e3
>     unify ty2 ty3
>     return ty3
> exprType tyEnv (Case _ alts) =
>   do
>     ty <- freshTypeVar
>     mapM_ (altType ty) alts
>     return ty
>   where altType ty (Alt _ _ rhs) = rhsType tyEnv rhs >>= unify ty

> rhsType :: ValueEnv -> Rhs -> TyState Type
> rhsType tyEnv (SimpleRhs _ e _) = exprType tyEnv e
> rhsType tyEnv (GuardedRhs es _) =
>   do
>     ty <- freshTypeVar
>     mapM_ (condExprType ty) es
>     return ty
>   where condExprType ty (CondExpr _ _ e) = exprType tyEnv e >>= unify ty

\end{verbatim}
In order to avoid name conflicts with non-generalized type variables
in a type we instantiate quantified type variables using non-negative
offsets here.
\begin{verbatim}

> freshTypeVar :: TyState Type
> freshTypeVar = liftM TypeVariable $ liftSt $ updateSt (1 +)

> instType :: Int -> Type -> TyState Type
> instType n ty =
>   do
>     tys <- sequence (replicate n freshTypeVar)
>     return (expandAliasType tys ty)

> instUniv :: TypeScheme -> TyState Type
> instUniv (ForAll n (QualType _ ty)) = instType n ty

\end{verbatim}
When unifying two types, the non-generalized variables, i.e.,
variables with negative offsets, must not be substituted. Otherwise,
the unification algorithm is identical to the one used by the type
checker.
\begin{verbatim}

> unify :: Type -> Type -> TyState ()
> unify ty1 ty2 =
>   updateSt_ (\theta -> unifyTypes (subst theta ty1) (subst theta ty2) theta)

> unifyList :: [Type] -> [Type] -> TyState ()
> unifyList tys1 tys2 = sequence_ (zipWith unify tys1 tys2)

> unifyArrow :: Type -> TyState (Type,Type)
> unifyArrow ty =
>   do
>     theta <- fetchSt
>     case subst theta ty of
>       TypeVariable tv
>         | tv >= 0 ->
>             do
>               ty1 <- freshTypeVar
>               ty2 <- freshTypeVar
>               updateSt_ (bindVar tv (TypeArrow ty1 ty2))
>               return (ty1,ty2)
>       TypeArrow ty1 ty2 -> return (ty1,ty2)
>       ty' -> internalError ("unifyArrow (" ++ show ty' ++ ")")

> unifyArrow2 :: Type -> TyState (Type,Type,Type)
> unifyArrow2 ty =
>   do
>     (ty1,ty2) <- unifyArrow ty
>     (ty21,ty22) <- unifyArrow ty2
>     return (ty1,ty21,ty22)

> unifyTypes :: Type -> Type -> TypeSubst -> TypeSubst
> unifyTypes (TypeVariable tv1) (TypeVariable tv2) theta
>   | tv1 == tv2 = theta
> unifyTypes (TypeVariable tv) ty theta
>   | tv >= 0 = bindVar tv ty theta
> unifyTypes ty (TypeVariable tv) theta
>   | tv >= 0 = bindVar tv ty theta
> unifyTypes (TypeConstructor tc1 tys1) (TypeConstructor tc2 tys2) theta
>   | tc1 == tc2 = unifyTypeLists tys1 tys2 theta
> unifyTypes (TypeConstrained tys1 tv1) (TypeConstrained tys2 tv2) theta
>   | tv1 == tv2 = theta
> unifyTypes (TypeArrow ty11 ty12) (TypeArrow ty21 ty22) theta =
>   unifyTypeLists [ty11,ty12] [ty21,ty22] theta
> unifyTypes (TypeSkolem k1) (TypeSkolem k2) theta
>   | k1 == k2 = theta
> unifyTypes ty1 ty2 _ =
>   internalError ("unify: (" ++ show ty1 ++ ") (" ++ show ty2 ++ ")")

> unifyTypeLists :: [Type] -> [Type] -> TypeSubst -> TypeSubst
> unifyTypeLists [] [] theta = theta
> unifyTypeLists (ty1:tys1) (ty2:tys2) theta =
>   unifyTypes (subst theta' ty1) (subst theta' ty2) theta'
>   where theta' = unifyTypeLists tys1 tys2 theta

\end{verbatim}
