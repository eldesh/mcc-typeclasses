% -*- LaTeX -*-
% $Id: Typing.lhs 2696 2008-05-09 19:05:03Z wlux $
%
% Copyright (c) 2003-2008, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Typing.lhs}
\section{Computing the Type of Curry Expressions}
\begin{verbatim}

> module Typing(Typeable(..), NewtypeEnv, newtypeEnv, etaType,
>               withType, matchType, argumentTypes) where
> import Base
> import Curry
> import CurryUtils
> import Env
> import Maybe
> import PredefIdent
> import PredefTypes
> import TopEnv
> import Types
> import TypeSubst
> import ValueInfo

\end{verbatim}
After the compiler has attributed patterns and expressions with type
information during type inference, it is straightforward to recompute
the type of every pattern and expression. Since all annotated types
are monomorphic, there is no need to instantiate any variables or
perform any (non-trivial) unifications.
\begin{verbatim}

> class Typeable a where
>   typeOf :: a -> Type

> instance Typeable Type where
>   typeOf = id

> instance Typeable a => Typeable (ConstrTerm a) where
>   typeOf (LiteralPattern a _) = typeOf a
>   typeOf (NegativePattern a _) = typeOf a
>   typeOf (VariablePattern a _) = typeOf a
>   typeOf (ConstructorPattern a _ _) = typeOf a
>   typeOf (InfixPattern a _ _ _) = typeOf a
>   typeOf (ParenPattern t) = typeOf t
>   typeOf (RecordPattern a _ _) = typeOf a
>   typeOf (TuplePattern ts) = tupleType (map typeOf ts)
>   typeOf (ListPattern a _) = typeOf a
>   typeOf (AsPattern _ t) = typeOf t
>   typeOf (LazyPattern t) = typeOf t

> instance Typeable a => Typeable (Expression a) where
>   typeOf (Literal a _) = typeOf a
>   typeOf (Variable a _) = typeOf a
>   typeOf (Constructor a _) = typeOf a
>   typeOf (Paren e) = typeOf e
>   typeOf (Typed e _) = typeOf e
>   typeOf (Record a _ _) = typeOf a
>   typeOf (RecordUpdate e _) = typeOf e
>   typeOf (Tuple es) = tupleType (map typeOf es)
>   typeOf (List a _) = typeOf a
>   typeOf (ListCompr e _) = listType (typeOf e)
>   typeOf (EnumFrom e) = listType (typeOf e)
>   typeOf (EnumFromThen e _) = listType (typeOf e)
>   typeOf (EnumFromTo e _) = listType (typeOf e)
>   typeOf (EnumFromThenTo e _ _) = listType (typeOf e)
>   typeOf (UnaryMinus e) = typeOf e
>   typeOf (Apply e _) =
>     case typeOf e of
>       TypeArrow _ ty -> ty
>       _ -> internalError "typeOf (Apply)"
>   typeOf (InfixApply _ op _) =
>     case typeOf (infixOp op) of
>       TypeArrow _ (TypeArrow _ ty) -> ty
>       _ -> internalError "typeOf (InfixApply)"
>   typeOf (LeftSection _ op) =
>     case typeOf (infixOp op) of
>       TypeArrow _ ty -> ty
>       _ -> internalError "typeOf (LeftSection)"
>   typeOf (RightSection op _) =
>     case typeOf (infixOp op) of
>       TypeArrow ty1 (TypeArrow _ ty2) -> TypeArrow ty1 ty2
>       _ -> internalError "typeOf (RightSection)"
>   typeOf (Lambda _ ts e) = foldr (TypeArrow . typeOf) (typeOf e) ts
>   typeOf (Let _ e) = typeOf e
>   typeOf (Do _ e) = typeOf e
>   typeOf (IfThenElse _ e _) = typeOf e
>   typeOf (Case _ as) = head [typeOf rhs | Alt _ _ rhs <- as]
>   typeOf (Fcase _ as) = head [typeOf rhs | Alt _ _ rhs <- as]

> instance Typeable a => Typeable (Rhs a) where
>   typeOf (SimpleRhs _ e _) = typeOf e
>   typeOf (GuardedRhs es _) = head [typeOf e | CondExpr _ _ e <- es]

\end{verbatim}
During desugaring, the compiler will remove newtype constructors and
renaming types effectively become type synonyms. Therefore, given a
definition \texttt{newtype $T\,u_1\dots,u_n$ = $N\,\tau$}, the types
$T\,\tau_1\dots\tau_n$ and $\tau[u_1/\tau_1,\dots,u_n/\tau_n]$ are
considered equal. However, in contrast to type synonyms renaming types
can be recursive. Therefore, we expand renaming types lazily when
necessary with the help of an auxiliary environment that maps each
newtype type constructor $T$ onto the pair $(n,\tau)$. This
environment is initialized trivially from the value type environment and
Note that it always contains an entry for type \texttt{IO}, which is
assumed to be defined implicitly as
\begin{verbatim}
  newtype IO a = IO (World -> (a,World))
\end{verbatim}
for some abstract type \texttt{World} representing the state of the
external world.
\begin{verbatim}

> type NewtypeEnv = Env QualIdent (Int,Type)

> newtypeEnv :: ValueEnv -> NewtypeEnv
> newtypeEnv tyEnv = foldr bindNewtype initNewtypeEnv (allEntities tyEnv)
>   where initNewtypeEnv = bindEnv qIOId (1,ioType') emptyEnv
>         ioType' = TypeArrow worldType (tupleType [TypeVariable 0,worldType])
>         worldType = TypeConstructor (qualify (mkIdent "World"))
>         bindNewtype (DataConstructor _ _ _ _) = id
>         bindNewtype (NewtypeConstructor _ _ ty) = bindEnv tc (length tvs,ty1)
>           where TypeArrow ty1 ty2 = rawType ty
>                 (TypeConstructor tc,tvs) = unapplyType True ty2
>         bindNewtype (Value _ _ _) = id

> etaType :: NewtypeEnv -> Int -> Type -> Type
> etaType _ 0 ty = ty
> etaType nEnv n (TypeArrow ty1 ty2) = TypeArrow ty1 (etaType nEnv (n - 1) ty2)
> etaType nEnv n ty =
>   case unapplyType True ty of
>     (TypeConstructor tc,tys) ->
>       case lookupEnv tc nEnv of
>         Just (n,ty)
>           | n > n' -> ty
>           | n == n' -> etaType nEnv n (expandAliasType tys ty)
>           | otherwise -> internalError "etaType"
>           where n' = length tys
>         Nothing -> ty
>     _ -> ty

\end{verbatim}
When inlining variable and function definitions, the compiler must
eventually update the type annotations of the inlined expression. To
that end, the variable or function's annotated type and the type of
the inlined expression must be unified. Since the program is type
correct, this unification is just a simple one way matching where we
only need to match the type variables in the inlined expression's type
with the corresponding types in the variable or function's annotated
type. However, we may need to expand renaming types since these
effectively become type synonyms after desugaring.

\ToDo{We would like to use the more general type signature
  \texttt{(Functor f,Typeable (f Type)) => NewtypeEnv -> Type -> f
    Type -> f Type} for \texttt{withType}. Unfortunately, nhc98 at
  present supports only simple class constraints, i.e., constraints
  where the constrained type is a type variable.}
\begin{verbatim}

> withType :: NewtypeEnv -> Type -> Expression Type -> Expression Type
> withType nEnv ty x = fmap (subst (matchType nEnv (typeOf x) ty idSubst)) x

> matchType :: NewtypeEnv -> Type -> Type -> TypeSubst -> TypeSubst
> matchType nEnv ty1 ty2 =
>   foldr (flip fromMaybe) (noMatch ty1 ty2)
>         [matchTypeApp nEnv ty1 ty2 | ty1 <- tys1, ty2 <- tys2]
>   where tys1 = expand nEnv ty1
>         tys2 = expand nEnv ty2
>         noMatch ty1 ty2 = internalError $
>           "matchType " ++ showsPrec 11 ty1 " " ++ showsPrec 11 ty2 ""

> matchTypeApp :: NewtypeEnv -> Type -> Type -> Maybe (TypeSubst -> TypeSubst)
> matchTypeApp _ (TypeVariable tv) ty
>   | ty == TypeVariable tv = Just id
>   | otherwise = Just (bindSubst tv ty)
> matchTypeApp _ (TypeConstructor tc1) (TypeConstructor tc2)
>   | tc1 == tc2 = Just id
> matchTypeApp _ (TypeConstrained _ tv1) (TypeConstrained _ tv2)
>   | tv1 == tv2 = Just id
> matchTypeApp _ (TypeSkolem k1) (TypeSkolem k2)
>   | k1 == k2 = Just id
> matchTypeApp nEnv (TypeApply ty11 ty12) (TypeApply ty21 ty22) =
>   fmap (. matchType nEnv ty12 ty22) (matchTypeApp nEnv ty11 ty21)
> matchTypeApp nEnv (TypeArrow ty11 ty12) (TypeArrow ty21 ty22) =
>   Just (matchType nEnv ty11 ty21 . matchType nEnv ty12 ty22)
> matchTypeApp nEnv (TypeApply ty11 ty12) (TypeArrow ty21 ty22) =
>   fmap (. matchType nEnv ty12 ty22)
>        (matchTypeApp nEnv ty11 (TypeApply (TypeConstructor qArrowId) ty21))
> matchTypeApp nEnv (TypeArrow ty11 ty12) (TypeApply ty21 ty22) =
>   fmap (. matchType nEnv ty12 ty22)
>        (matchTypeApp nEnv (TypeApply (TypeConstructor qArrowId) ty11) ty21)
> matchTypeApp _ _ _ = Nothing

> expand :: NewtypeEnv -> Type -> [Type]
> expand nEnv ty = ty : uncurry (expandType nEnv) (unapplyType False ty)
>   where expandType nEnv (TypeConstructor tc) tys =
>           case lookupEnv tc nEnv of
>             Just (n,ty)
>               | n > n' -> []
>               | n == n' -> expand (unbindEnv tc nEnv) (expandAliasType tys ty)
>               | otherwise -> internalError "expand"
>               where n' = length tys
>             Nothing -> []
>         expandType _ _ _ = []

\end{verbatim}
The function \texttt{argumentTypes} returns the labels and the
argument types of a data constructor instantiated at a particular
type. This function is useful for desugaring record patterns and
expressions, where the compiler must compute the types of the omitted
arguments. Since the type annotation of record patterns and
expressions applies to the pattern or expression as a whole, the
instance type is unified with the constructor's result type and the
resulting substitution is applied to all argument types. Note that
this is sound because record fields cannot have existentially
quantified types and therefore all type variables appearing in their
types occur in the constructor's result type as well. We assume that
newtype constructors have not yet been replaced when this function is
used.
\begin{verbatim}

> argumentTypes :: Type -> QualIdent -> ValueEnv -> ([Ident],[Type])
> argumentTypes ty c tyEnv =
>   (ls,map (subst (matchType (newtypeEnv tyEnv) ty0 ty idSubst)) tys)
>   where (ls,_,ty') = conType c tyEnv
>         (tys,ty0) = arrowUnapply (rawType ty')

\end{verbatim}
