% -*- LaTeX -*-
% $Id: Newtype.lhs 2981 2010-07-09 14:00:25Z wlux $
%
% Copyright (c) 2009-2010, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Newtype.lhs}
\section{Removing Newtype Constructors}
A newtype declaration \texttt{newtype} $T\;x_1\dots x_n$ \texttt{=}
$N\;\tau$ introduces a new, distinct type whose representation is the
same as that of type $\tau$. In contrast to a data type declaration,
the newtype constructor $N$ is transparent with respect to the
operational semantics. Therefore, the compiler replaces patterns
$N\;t$ and expressions $N\;e$, where $N$ is a newtype constructor, by
their respective arguments $t$ and $e$. In order to handle partial
applications of newtype constructors in expressions, the compiler
replaces the newtype declaration by a function declaration $N\;x$
\texttt{=} $x$. In addition, a type synonym declaration \texttt{type}
$T\;x_1\dots x_n$ \texttt{=} $\tau$ is added to the code. Note that
this means that the compiler now must be able to deal with (mutually)
recursive type synonyms, which are not allowed in source code.
\begin{verbatim}

> module Newtype(transNewtype) where
> import Combined
> import Curry
> import CurryUtils
> import Kinds
> import List
> import Monad
> import PredefIdent
> import PredefTypes
> import TopEnv
> import Types
> import TypeInfo
> import Utils
> import ValueInfo

\end{verbatim}
New identifiers are introduced in the definitions of the functions
replacing newtype declarations. Once more, we use a state monad
transformer to generate unique names.
\begin{verbatim}

> type NewtypeState a = StateT Int Id a

> transNewtype :: TCEnv -> ValueEnv -> Module QualType
>              -> (TCEnv,ValueEnv,Module QualType)
> transNewtype tcEnv tyEnv (Module m es is ds) =
>   (bindWorld (fmap (transTypeInfo tyEnv) tcEnv),
>    fmap transValueInfo tyEnv,
>    Module m es is (concat (runSt (mapM (transTopDecl m tyEnv) ds) 1)))

\end{verbatim}
Besides user defined renaming types, the compiler also considers the
built-in type \texttt{IO} a renaming type that is supposed to be
defined via \texttt{newtype IO a = IO (World -> (a,World))}, where
\texttt{World} is an abstract type representing the state of the
external world. Actually, the runtime system uses a slightly more
efficient representation for \texttt{IO} (cf.\ 
Sect.~\ref{sec:io-monad}), but it is sufficently similar to the one
used here. Note that we do not add the constructor \texttt{IO} to the
value type environment because it is never used in source code.

\ToDo{Make the definition of \texttt{IO} apparent in source code to
  get rid of this hack.}
\begin{verbatim}

> bindWorld :: TCEnv -> TCEnv
> bindWorld = qualImportTopEnv qWorldId (DataType qWorldId KindStar [])

> transTypeInfo :: ValueEnv -> TypeInfo -> TypeInfo
> transTypeInfo _ (DataType tc k cs)
>   | tc == qIOId = AliasType tc (kindArity k) k ioType'
>   | otherwise = DataType tc k cs
>   where ioType' = TypeArrow worldType (tupleType [TypeVariable 0,worldType])
>         worldType = TypeConstructor qWorldId
> transTypeInfo tyEnv (RenamingType tc k c) = AliasType tc (kindArity k) k ty
>   where ty = arrowDomain (rawConType (qualifyLike tc c) tyEnv)
> transTypeInfo _ (AliasType tc n k ty) = AliasType tc n k ty
> transTypeInfo _ (TypeClass cls k clss fs) = TypeClass cls k clss fs

> transValueInfo :: ValueInfo -> ValueInfo
> transValueInfo (DataConstructor c ls ci ty) = DataConstructor c ls ci ty
> transValueInfo (NewtypeConstructor c _ ty) = Value c 1 ty
> transValueInfo (Value f n ty) = Value f n ty

\end{verbatim}
At the top-level, each newtype declaration is replaced by a type
synonym declaration and a function declaration.
\begin{verbatim}

> transTopDecl :: ModuleIdent -> ValueEnv -> TopDecl QualType
>              -> NewtypeState [TopDecl QualType]
> transTopDecl _ _ (DataDecl p cx tc tvs cs clss) =
>   return [DataDecl p cx tc tvs cs clss]
> transTopDecl m tyEnv (NewtypeDecl p _ tc tvs (NewConstrDecl _ c ty) _) =
>   do
>     v <- freshVar "_#v" (instType (arrowDomain ty'))
>     let d =
>           funDecl p (qualType ty') c [uncurry VariablePattern v]
>                   (uncurry mkVar v)
>     return [TypeDecl p tc tvs ty,BlockDecl d]
>   where ty' = rawConType (qualifyWith m c) tyEnv
> transTopDecl _ _ (TypeDecl p tc tvs ty) = return [TypeDecl p tc tvs ty]
> transTopDecl _ tyEnv (ClassDecl p cx cls tv ds) =
>   return [ClassDecl p cx cls tv (tds ++ transNewt tyEnv vds)]
>   where (tds,vds) = partition isTypeSig ds
> transTopDecl _ tyEnv (InstanceDecl p cx cls ty ds) =
>   return [InstanceDecl p cx cls ty (transNewt tyEnv ds)]
> transTopDecl _ _ (DefaultDecl p tys) = return [DefaultDecl p tys]
> transTopDecl _ tyEnv (BlockDecl d) = return [BlockDecl (transNewt tyEnv d)]
> transTopDecl _ _ (SplitAnnot p) = return [SplitAnnot p]

\end{verbatim}
Apart from that, the compiler simply descends the syntax tree and
removes newtype constructors in patterns and expressions.
\begin{verbatim}

> class SyntaxTree a where
>   transNewt :: ValueEnv -> a -> a

> instance SyntaxTree a => SyntaxTree [a] where
>   transNewt tyEnv = map (transNewt tyEnv)

> instance SyntaxTree (Decl a) where
>   transNewt tyEnv (FunctionDecl p ty f eqs) =
>     FunctionDecl p ty f (transNewt tyEnv eqs)
>   transNewt _ (ForeignDecl p fi ty f ty') = ForeignDecl p fi ty f ty'
>   transNewt tyEnv (PatternDecl p t rhs) =
>     PatternDecl p (transNewt tyEnv t) (transNewt tyEnv rhs)
>   transNewt _ (FreeDecl p vs) = FreeDecl p vs

> instance SyntaxTree (Equation a) where
>   transNewt tyEnv (Equation p lhs rhs) =
>     Equation p (transNewt tyEnv lhs) (transNewt tyEnv rhs)

> instance SyntaxTree (Lhs a) where
>   transNewt tyEnv (FunLhs f ts) = FunLhs f (transNewt tyEnv ts)

> instance SyntaxTree (ConstrTerm a) where
>   transNewt _ (LiteralPattern ty l) = LiteralPattern ty l
>   transNewt _ (VariablePattern ty v) = VariablePattern ty v
>   transNewt tyEnv (ConstructorPattern ty c ts) =
>     case ts of
>       [t]
>         | isNewtypeConstr tyEnv c -> transNewt tyEnv t
>         | otherwise -> ConstructorPattern ty c [transNewt tyEnv t]
>       _ -> ConstructorPattern ty c (transNewt tyEnv ts)
>   transNewt tyEnv (FunctionPattern ty f ts) =
>     FunctionPattern ty f (transNewt tyEnv ts)
>   transNewt tyEnv (AsPattern v t) = AsPattern v (transNewt tyEnv t)
>   transNewt tyEnv (LazyPattern t) = LazyPattern (transNewt tyEnv t)

> instance SyntaxTree (Rhs a) where
>   transNewt tyEnv (SimpleRhs p e ds) =
>     SimpleRhs p (transNewt tyEnv e) (transNewt tyEnv ds)
>   transNewt tyEnv (GuardedRhs es ds) =
>     GuardedRhs (transNewt tyEnv es) (transNewt tyEnv ds)

> instance SyntaxTree (CondExpr a) where
>   transNewt tyEnv (CondExpr p g e) =
>     CondExpr p (transNewt tyEnv g) (transNewt tyEnv e)

> instance SyntaxTree (Expression a) where
>   transNewt _ (Literal ty l) = Literal ty l
>   transNewt _ (Variable ty v) = Variable ty v
>   transNewt tyEnv (Constructor ty c)
>     | isNewtypeConstr tyEnv c = Variable ty c
>     | otherwise = Constructor ty c
>   transNewt tyEnv (Apply e1 e2) =
>     case e1 of
>       Constructor ty c
>         | isNewtypeConstr tyEnv c -> transNewt tyEnv e2
>         | otherwise -> Apply (Constructor ty c) (transNewt tyEnv e2)
>       _ -> Apply (transNewt tyEnv e1) (transNewt tyEnv e2)
>   transNewt tyEnv (Lambda p ts e) =
>     Lambda p (transNewt tyEnv ts) (transNewt tyEnv e)
>   transNewt tyEnv (Let ds e) = Let (transNewt tyEnv ds) (transNewt tyEnv e)
>   transNewt tyEnv (Case e as) = Case (transNewt tyEnv e) (transNewt tyEnv as)
>   transNewt tyEnv (Fcase e as) =
>     Fcase (transNewt tyEnv e) (transNewt tyEnv as)

> instance SyntaxTree (Alt a) where
>   transNewt tyEnv (Alt p t rhs) =
>     Alt p (transNewt tyEnv t) (transNewt tyEnv rhs)

\end{verbatim}
The function \texttt{rawConType} returns the raw type of a (newtype)
constructor and the function \texttt{arrowDomain} returns the domain
of an arrow type, i.e., its argument type.
\begin{verbatim}

> rawConType :: QualIdent -> ValueEnv -> Type
> rawConType c tyEnv = rawType (thd3 (conType c tyEnv))

> arrowDomain :: Type -> Type
> arrowDomain (TypeArrow ty _) = ty

\end{verbatim}
The function \texttt{instType} instantiates the universally quantified
type variables of a type (scheme) with fresh type variables. Since
this function is used only to instantiate the closed types of newtype
constructors, the compiler can reuse the same monomorphic type
variables for every instantiated type.
\begin{verbatim}

> instType :: Type -> Type
> instType (TypeConstructor tc) = TypeConstructor tc
> instType (TypeVariable tv) = TypeVariable (-1 - tv)
> instType (TypeArrow ty1 ty2) = TypeArrow (instType ty1) (instType ty2)
> instType (TypeApply ty1 ty2) = TypeApply (instType ty1) (instType ty2)

\end{verbatim}
Generation of fresh names.
\begin{verbatim}

> freshVar :: String -> Type -> NewtypeState (QualType,Ident)
> freshVar prefix ty =
>   do
>     v <- liftM (mkName prefix) (updateSt (1 +))
>     return (qualType ty,v)
>   where mkName pre n = renameIdent (mkIdent (pre ++ show n)) n

\end{verbatim}
Auxiliary functions.
\begin{verbatim}

> qWorldId :: QualIdent
> qWorldId = qualify (mkIdent "World")

\end{verbatim}
