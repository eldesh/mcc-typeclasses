% -*- LaTeX -*-
% $Id: Newtype.lhs 2799 2009-04-26 16:24:46Z wlux $
%
% Copyright (c) 2009, Wolfgang Lux
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

> transNewtype :: TCEnv -> ValueEnv -> Module Type
>              -> (Module Type,TCEnv,ValueEnv)
> transNewtype tcEnv tyEnv (Module m es is ds) =
>   (Module m es is ds',bindWorld (fmap (transTypeInfo tyEnv) tcEnv),tyEnv')
>   where (ds',tyEnv') =
>           run (transModule m tyEnv ds) (fmap transValueInfo tyEnv)

\end{verbatim}
New identifiers are introduced in the definitions of the functions
replacing newtype declarations. Once more, we use nested state monad
transformers in order to generate unique names and pass through the
type environment, which is augmented with the types of the new
variables.
\begin{verbatim}

> type NewtypeState a = StateT ValueEnv (StateT Int Id) a

> run :: NewtypeState a -> ValueEnv -> a
> run m tyEnv = runSt (callSt m tyEnv) 1

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
> bindWorld =
>   qualImportTopEnv (mkMIdent []) qWorldId (DataType qWorldId KindStar [])

> transTypeInfo :: ValueEnv -> TypeInfo -> TypeInfo
> transTypeInfo _ (DataType tc k cs)
>   | tc == qIOId = AliasType tc (kindArity k) k ioType'
>   | otherwise = DataType tc k cs
>   where ioType' = TypeArrow worldType (tupleType [TypeVariable 0,worldType])
>         worldType = TypeConstructor qWorldId
> transTypeInfo tyEnv (RenamingType tc k c) =
>   AliasType tc (kindArity k) k (reprType (qualifyLike tc c) tyEnv)
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

> transModule :: ModuleIdent -> ValueEnv -> [TopDecl Type]
>             -> NewtypeState ([TopDecl Type],ValueEnv)
> transModule m tyEnv ds =
>   do
>     dss' <- mapM (transTopDecl m tyEnv) ds
>     tyEnv' <- fetchSt
>     return (concat dss',tyEnv')

> transTopDecl :: ModuleIdent -> ValueEnv -> TopDecl Type
>              -> NewtypeState [TopDecl Type]
> transTopDecl _ _ (DataDecl p cx tc tvs cs clss) =
>   return [DataDecl p cx tc tvs cs clss]
> transTopDecl m tyEnv (NewtypeDecl p _ tc tvs (NewConstrDecl _ c ty) _) =
>   do
>     v <- freshVar m "_#v" (reprType (qualifyWith m c) tyEnv)
>     let d = funDecl p c [uncurry VariablePattern v] (uncurry mkVar v)
>     return [TypeDecl p tc tvs ty,BlockDecl d]
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
>   transNewt tyEnv (FunctionDecl p f eqs) =
>     FunctionDecl p f (transNewt tyEnv eqs)
>   transNewt _ (ForeignDecl p cc s ie f ty) = ForeignDecl p cc s ie f ty
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
>   transNewt tyEnv (AsPattern v t) = AsPattern v (transNewt tyEnv t)

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
>   transNewt tyEnv (IfThenElse e1 e2 e3) =
>     IfThenElse (transNewt tyEnv e1) (transNewt tyEnv e2) (transNewt tyEnv e3)
>   transNewt tyEnv (Case e as) = Case (transNewt tyEnv e) (transNewt tyEnv as)
>   transNewt tyEnv (Fcase e as) =
>     Fcase (transNewt tyEnv e) (transNewt tyEnv as)

> instance SyntaxTree (Alt a) where
>   transNewt tyEnv (Alt p t rhs) =
>     Alt p (transNewt tyEnv t) (transNewt tyEnv rhs)

\end{verbatim}
The function \texttt{reprType} returns the representation type of a
renaming type, which is just the codomain of its constructor's type.
\begin{verbatim}

> reprType :: QualIdent -> ValueEnv -> Type
> reprType c tyEnv = ty
>   where TypeArrow ty _ = rawType (thd3 (conType c tyEnv))

\end{verbatim}
Generation of fresh names.
\begin{verbatim}

> freshVar :: ModuleIdent -> String -> Type -> NewtypeState (Type,Ident)
> freshVar m prefix ty =
>   do
>     v <- liftM (mkName prefix) (liftSt (updateSt (1 +)))
>     updateSt_ (bindFun m v 0 (monoType ty))
>     return (ty,v)
>   where mkName pre n = mkIdent (pre ++ show n)

\end{verbatim}
Auxiliary functions.
\begin{verbatim}

> qWorldId :: QualIdent
> qWorldId = qualify (mkIdent "World")

\end{verbatim}
