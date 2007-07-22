% -*- LaTeX -*-
% $Id: Typing.lhs 2408 2007-07-22 21:51:27Z wlux $
%
% Copyright (c) 2003-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Typing.lhs}
\section{Computing the Type of Curry Expressions}
\begin{verbatim}

> module Typing(Typeable(..), NewtypeEnv, newtypeEnv, matchType) where
> import Base
> import Env
> import Maybe
> import TopEnv
> import TypeSubst

\end{verbatim}
After the compiler has attributed patterns and expressions with type
information during type inference, it is straight forward to recompute
the type of every pattern and expression. Since all annotated types
are monomorphic, there is no need to instantiate any variables or
perform any (non-trivial) unifications.
\begin{verbatim}

> class Typeable a where
>   typeOf :: a -> Type

> instance Typeable Type where
>   typeOf = id

> instance Typeable a => Typeable (ConstrTerm a) where
>   typeOf = argType

> instance Typeable a => Typeable (Expression a) where
>   typeOf = exprType

> instance Typeable a => Typeable (Rhs a) where
>   typeOf = rhsType

> argType :: Typeable a => ConstrTerm a -> Type
> argType (LiteralPattern a _) = typeOf a
> argType (NegativePattern a _) = typeOf a
> argType (VariablePattern a _) = typeOf a
> argType (ConstructorPattern a _ _) = typeOf a
> argType (InfixPattern a _ _ _) = typeOf a
> argType (ParenPattern t) = argType t
> argType (TuplePattern ts) = tupleType (map argType ts)
> argType (ListPattern a _) = typeOf a
> argType (AsPattern _ t) = argType t
> argType (LazyPattern t) = argType t

> exprType :: Typeable a => Expression a -> Type
> exprType (Literal a _) = typeOf a
> exprType (Variable a _) = typeOf a
> exprType (Constructor a _) = typeOf a
> exprType (Typed e _) = exprType e
> exprType (Paren e) = exprType e
> exprType (Tuple es) = tupleType (map exprType es)
> exprType (List a _) = typeOf a
> exprType (ListCompr e _) = listType (exprType e)
> exprType (EnumFrom e) = listType (exprType e)
> exprType (EnumFromThen e _) = listType (exprType e)
> exprType (EnumFromTo e _) = listType (exprType e)
> exprType (EnumFromThenTo e _ _) = listType (exprType e)
> exprType (UnaryMinus e) = exprType e
> exprType (Apply f e) =
>   case exprType f of
>     TypeArrow _ ty -> ty
>     _ -> internalError "exprType (Apply)"
> exprType (InfixApply e1 op e2) =
>   case exprType (infixOp op) of
>     TypeArrow _ (TypeArrow _ ty) -> ty
>     _ -> internalError "exprType (InfixApply)"
> exprType (LeftSection e op) =
>   case exprType (infixOp op) of
>     TypeArrow _ ty -> ty
>     _ -> internalError "exprType (LeftSection)"
> exprType (RightSection op e) =
>   case exprType (infixOp op) of
>     TypeArrow ty1 (TypeArrow _ ty2) -> TypeArrow ty1 ty2
>     _ -> internalError "exprType (RightSection)"
> exprType (Lambda _ ts e) = foldr TypeArrow (exprType e) (map argType ts)
> exprType (Let _ e) = exprType e
> exprType (Do _ e) = exprType e
> exprType (IfThenElse _ e _) = exprType e
> exprType (Case _ as) = head [rhsType rhs | Alt _ _ rhs <- as]

> rhsType :: Typeable a => Rhs a -> Type
> rhsType (SimpleRhs _ e _) = exprType e
> rhsType (GuardedRhs es _) = head [exprType e | CondExpr _ _ e <- es]

\end{verbatim}
During desugaring, the compiler will remove newtype constructors and
renaming types effectively become type synonyms. Therefore, given a
definition \texttt{newtype $T\,u_1\dots,u_n$ = $N\,\tau$}, the types
$T\,\tau_1\dots\tau_n$ and $\tau[u_1/\tau_1,\dots,u_n/\tau_n]$ are
considered equal. However, renaming types -- in contrast to type
synonyms -- can be recursive. Therefore, we expand renaming types
lazily with the help of an auxiliary environment that maps each
newtype type constructor $T$ onto the argument type $\tau$ of its
newtype constructor. This environment is initialized trivially from
the value type environment. Note that it always contains an entry for
type \texttt{IO}, which is assumed to be defined implicitly as
\begin{verbatim}
  newtype IO a = IO (World -> (a,World))
\end{verbatim}
for some abstract type \texttt{World} representing the state of the
external world.
\begin{verbatim}

> type NewtypeEnv = Env QualIdent Type

> newtypeEnv :: ValueEnv -> NewtypeEnv
> newtypeEnv tyEnv = foldr bindNewtype initNewtypeEnv (allEntities tyEnv)
>   where initNewtypeEnv = bindEnv qIOId ioType' emptyEnv
>         ioType' = TypeArrow worldType (tupleType [TypeVariable 0,worldType])
>         worldType = TypeConstructor (qualify (mkIdent "World"))
>         bindNewtype (DataConstructor _ _ _) = id
>         bindNewtype (NewtypeConstructor _ ty) = bindEnv (rootOfType ty2) ty1
>           where TypeArrow ty1 ty2 = rawType ty
>         bindNewtype (Value _ _ _) = id

\end{verbatim}
When inlining expressions, the compiler must also update the type
annotations of the inlined expression. To that end, the compiler must
unify the types of the old expression being subsituted and the new
expressions that is substituted for it. Since the program is type
correct, this matching amounts to a simple one way matching where we
only need to find for each type variable occurring in the type of the
new expression the matching type in the type of the old expression.
The only complication is that we eventually must expand newtypes in
order to match the two types. Note that the first type argument of
\texttt{matchType} is the type of the new expression.
\begin{verbatim}

> matchType :: NewtypeEnv -> Type -> Type -> TypeSubst -> TypeSubst
> matchType nEnv ty1 ty2 = matchTypeApp nEnv ty1 ty2 []

> matchTypeApp :: NewtypeEnv -> Type -> Type -> [(Type,Type)] -> TypeSubst
>              -> TypeSubst
> matchTypeApp nEnv (TypeVariable tv) ty tys
>   | ty == TypeVariable tv = matchTypes nEnv tys
>   | otherwise = bindSubst tv ty . matchTypes nEnv tys
> matchTypeApp nEnv (TypeConstructor tc1) (TypeConstructor tc2) tys
>   | tc1 == tc2 = matchTypes nEnv tys
> matchTypeApp nEnv (TypeConstrained tv1 _) (TypeConstrained tv2 _) tys
>   | tv1 == tv2 = matchTypes nEnv tys
> matchTypeApp nEnv (TypeSkolem k1) (TypeSkolem k2) tys
>   | k1 == k2 = matchTypes nEnv tys
> matchTypeApp nEnv (TypeApply ty11 ty12) (TypeApply ty21 ty22) tys =
>   matchTypeApp nEnv ty11 ty21 ((ty12,ty22) : tys)
> matchTypeApp nEnv (TypeArrow ty11 ty12) (TypeArrow ty21 ty22) tys =
>   matchType nEnv ty11 ty21 . matchType nEnv ty12 ty22 . matchTypes nEnv tys
> matchTypeApp nEnv (TypeConstructor tc) ty2 tys
>   | isJust n = matchType nEnv ty1' ty2'
>   where n = lookupEnv tc nEnv
>         ty1' = expandAliasType (map fst tys) (fromJust n)
>         ty2' = applyType ty2 (map snd tys)
> matchTypeApp nEnv ty1 (TypeConstructor tc) tys
>   | isJust n = matchType nEnv ty1' ty2'
>   where n = lookupEnv tc nEnv
>         ty1' = applyType ty1 (map fst tys)
>         ty2' = expandAliasType (map snd tys) (fromJust n)
> matchTypeApp _ ty1 ty2 tys =
>   internalError ("matchType (" ++ show ty1' ++ ") (" ++ show ty2' ++ ")")
>   where ty1' = applyType ty1 (map fst tys)
>         ty2' = applyType ty2 (map snd tys)

> matchTypes :: NewtypeEnv -> [(Type,Type)] -> TypeSubst -> TypeSubst
> matchTypes nEnv tys theta =
>   foldr (uncurry (matchType nEnv)) theta tys

\end{verbatim}

