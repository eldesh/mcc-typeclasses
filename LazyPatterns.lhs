% -*- LaTeX -*-
% $Id: LazyPatterns.lhs 2981 2010-07-09 14:00:25Z wlux $
%
% Copyright (c) 2001-2010, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{LazyPatterns.lhs}
\section{Desugaring Lazy Patterns}
Lazy patterns provide convenient syntactic sugar for matching
components of a data term without forcing evaluation of the term
before any of its components is used. This is similar to pattern
declarations and this compiler phase removes lazy patterns from the
compiled module by replacing each lazy pattern with a variable and a
pattern declaration that is in scope where the lazy pattern's
variables are in scope.
\begin{verbatim}

> module LazyPatterns(unlazy) where
> import Combined
> import Curry
> import CurryUtils
> import List
> import Monad
> import Types
> import Typing
> import Utils

\end{verbatim}
We use a state monad transformer for generating unique names for the
fresh variables replacing lazy patterns.
\begin{verbatim}

> type UnlazyState a = StateT Int Id a

> unlazy :: Module QualType -> Module QualType
> unlazy (Module m es is ds) =
>   Module m es is (concat (runSt (mapM unlazyTopDecl ds) 1))

\end{verbatim}
If a pattern declaration uses lazy patterns, its lifted declarations
become part of the same declaration group. Note that since pattern
bindings are evaluated lazily, their patterns are transformed like
lazy patterns.
\begin{verbatim}

> unlazyTopDecl :: TopDecl QualType -> UnlazyState [TopDecl QualType]
> unlazyTopDecl (DataDecl p cx tc tvs cs clss) =
>   return [DataDecl p cx tc tvs cs clss]
> unlazyTopDecl (NewtypeDecl p cx tc tvs nc clss) =
>   return [NewtypeDecl p cx tc tvs nc clss]
> unlazyTopDecl (TypeDecl p tc tvs ty) = return [TypeDecl p tc tvs ty]
> unlazyTopDecl (ClassDecl p cx cls tv ds) =
>   liftM (return . ClassDecl p cx cls tv . (tds ++) . concat)
>         (mapM unlazyDecl vds)
>   where (tds,vds) = partition isTypeSig ds
> unlazyTopDecl (InstanceDecl p cx cls ty ds) =
>   liftM (return . InstanceDecl p cx cls ty . concat) (mapM unlazyDecl ds)
> unlazyTopDecl (DefaultDecl p tys) = return [DefaultDecl p tys]
> unlazyTopDecl (BlockDecl d) = liftM (map BlockDecl) (unlazyDecl d)
> unlazyTopDecl (SplitAnnot p) = return [SplitAnnot p]

> unlazyDecl :: Decl QualType -> UnlazyState [Decl QualType]
> unlazyDecl (FunctionDecl p ty f eqs) =
>   liftM (return . FunctionDecl p ty f) (mapM unlazyEquation eqs)
> unlazyDecl (ForeignDecl p fi ty f ty') = return [ForeignDecl p fi ty f ty']
> unlazyDecl (PatternDecl p t rhs) =
>   do
>     (ds',t') <- liftLazy p [] (lazyTerm t)
>     rhs' <- unlazyRhs rhs
>     return (PatternDecl p t' rhs' : ds')
> unlazyDecl (FreeDecl p vs) = return [FreeDecl p vs]

> unlazyEquation :: Equation QualType -> UnlazyState (Equation QualType)
> unlazyEquation (Equation p (FunLhs f ts) rhs) =
>   do
>     (ds',ts') <- mapAccumM (liftLazy p) [] (map unlazyTerm ts)
>     rhs' <- unlazyRhs rhs
>     return (Equation p (FunLhs f ts') (addDecls ds' rhs'))

\end{verbatim}
The transformation of lazy patterns is performed in two steps. First,
the compiler removes redundant lazy patterns, where a lazy pattern
\texttt{\char`\~$t$} is redundant if the base pattern $t$ is already
an irrefutable pattern, i.e., either a variable pattern, another lazy
pattern, or an as-pattern $v$\texttt{@}$t$ where $t$ is irrefutable
itself.\footnote{If this transformation were performed before removing
  newtype constructors, we would also consider patterns of the form
  $N\;t$ irrefutable when $N$ is a newtype constructor and $t$ is
  irrefutable.}
\begin{verbatim}

> unlazyTerm :: ConstrTerm a -> ConstrTerm a
> unlazyTerm (LiteralPattern ty l) = LiteralPattern ty l
> unlazyTerm (VariablePattern ty v) = VariablePattern ty v
> unlazyTerm (ConstructorPattern ty c ts) =
>   ConstructorPattern ty c (map unlazyTerm ts)
> unlazyTerm (FunctionPattern ty f ts) =
>   FunctionPattern ty f (map unlazyTerm ts)
> unlazyTerm (AsPattern v t) = AsPattern v (unlazyTerm t)
> unlazyTerm (LazyPattern t) = lazyPattern (lazyTerm t)
>   where lazyPattern t = if isIrrefutable t then t else LazyPattern t

> lazyTerm :: ConstrTerm a -> ConstrTerm a
> lazyTerm t =
>   case t of
>     LazyPattern t' -> lazyTerm t'
>     _ -> unlazyTerm t

> isIrrefutable :: ConstrTerm a -> Bool
> isIrrefutable (LiteralPattern _ _) = False
> isIrrefutable (VariablePattern _ _) = True
> isIrrefutable (ConstructorPattern _ _ _) = False
> isIrrefutable (FunctionPattern _ _ _) = False
> isIrrefutable (AsPattern _ t) = isIrrefutable t
> isIrrefutable (LazyPattern _) = True

\end{verbatim}
After removing redundant lazy patterns, the second phase of the
transformation replaces each remaining lazy pattern
\texttt{\char`\~$t$} by a (fresh) variable $v$ and a pattern
declaration $t$~\texttt{=}~$v$. As a minor optimization, the compiler
reuses the pattern variable $v$ when transforming a pattern of the
form \texttt{$v$@(\char`\~$t$)}.

Note the subtle difference between the patterns
\texttt{\char`\~($v$@$t$)} and \texttt{$v$@(\char`\~$t$)}. For the
former, the value bound to $v$ is matched against $t$ when $v$ is
evaluated, whereas this is not the case for the latter. Therefore, we
must introduce a fresh variable when transforming a pattern of the
form \texttt{\char`\~($v$@$t$)}.
\begin{verbatim}

> liftLazy :: Position -> [Decl QualType] -> ConstrTerm QualType
>          -> UnlazyState ([Decl QualType],ConstrTerm QualType)
> liftLazy _ ds (LiteralPattern ty l) = return (ds,LiteralPattern ty l)
> liftLazy _ ds (VariablePattern ty v) = return (ds,VariablePattern ty v)
> liftLazy p ds (ConstructorPattern ty c ts) =
>   liftM (apSnd (ConstructorPattern ty c)) (mapAccumM (liftLazy p) ds ts)
> liftLazy p ds (FunctionPattern ty f ts) =
>   liftM (apSnd (FunctionPattern ty f)) (mapAccumM (liftLazy p) ds ts)
> liftLazy p ds (AsPattern v t) =
>   case t of
>     LazyPattern t' -> liftM (liftPattern p (ty,v)) (liftLazy p ds t')
>       where ty = qualType (typeOf t')
>     _ -> liftM (apSnd (AsPattern v)) (liftLazy p ds t)
> liftLazy p ds (LazyPattern t) =
>   liftM2 (liftPattern p) (freshVar "_#lazy" (typeOf t)) (liftLazy p ds t)

> liftPattern :: Position -> (a,Ident) -> ([Decl a],ConstrTerm a)
>             -> ([Decl a],ConstrTerm a)
> liftPattern p v (ds,t) =
>   (patDecl p t (uncurry mkVar v) : ds,uncurry VariablePattern v)

\end{verbatim}
Lifted declarations for lazy patterns in lambda expressions and case
alternatives are added to the body of the expression.
\begin{verbatim}

> unlazyRhs :: Rhs QualType -> UnlazyState (Rhs QualType)
> unlazyRhs (SimpleRhs p e ds) =
>   do
>     dss' <- mapM unlazyDecl ds
>     e' <- unlazyExpr e
>     return (SimpleRhs p e' (concat dss'))
> unlazyRhs (GuardedRhs es ds) =
>   do
>     dss' <- mapM unlazyDecl ds
>     es' <- mapM unlazyCondExpr es
>     return (GuardedRhs es' (concat dss'))

> unlazyCondExpr :: CondExpr QualType -> UnlazyState (CondExpr QualType)
> unlazyCondExpr (CondExpr p g e) =
>   liftM2 (CondExpr p) (unlazyExpr g) (unlazyExpr e)

> unlazyExpr :: Expression QualType -> UnlazyState (Expression QualType)
> unlazyExpr (Literal ty l) = return (Literal ty l)
> unlazyExpr (Variable ty v) = return (Variable ty v)
> unlazyExpr (Constructor ty c) = return (Constructor ty c)
> unlazyExpr (Apply e1 e2) = liftM2 Apply (unlazyExpr e1) (unlazyExpr e2)
> unlazyExpr (Lambda p ts e) =
>   do
>     (ds',ts') <- mapAccumM (liftLazy p) [] (map unlazyTerm ts)
>     e' <- unlazyExpr e
>     return (Lambda p ts' (mkLet ds' e'))
> unlazyExpr (Let ds e) =
>   liftM2 (Let . concat) (mapM unlazyDecl ds) (unlazyExpr e)
> unlazyExpr (Case e as) = liftM2 Case (unlazyExpr e) (mapM unlazyAlt as)
> unlazyExpr (Fcase e as) = liftM2 Fcase (unlazyExpr e) (mapM unlazyAlt as)

> unlazyAlt :: Alt QualType -> UnlazyState (Alt QualType)
> unlazyAlt (Alt p t rhs) =
>   do
>     (ds',t') <- liftLazy p [] (unlazyTerm t)
>     rhs' <- unlazyRhs rhs
>     return (Alt p t' (addDecls ds' rhs'))

\end{verbatim}
Generation of fresh names.
\begin{verbatim}

> freshVar :: String -> Type -> UnlazyState (QualType,Ident)
> freshVar prefix ty =
>   do
>     v <- liftM (mkName prefix) (updateSt (1 +))
>     return (qualType ty,v)
>   where mkName pre n = renameIdent (mkIdent (pre ++ show n)) n

\end{verbatim}
Auxiliary definitions.
\begin{verbatim}

> addDecls :: [Decl a] -> Rhs a -> Rhs a
> addDecls ds (SimpleRhs p e ds') = SimpleRhs p e (ds ++ ds')
> addDecls ds (GuardedRhs es ds') = GuardedRhs es (ds ++ ds')

\end{verbatim}
