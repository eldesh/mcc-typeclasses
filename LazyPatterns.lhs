% -*- LaTeX -*-
% $Id: LazyPatterns.lhs 2809 2009-04-29 13:11:20Z wlux $
%
% Copyright (c) 2001-2009, Wolfgang Lux
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
> import ValueInfo

> unlazy :: ValueEnv -> Module Type -> (Module Type,ValueEnv)
> unlazy tyEnv (Module m es is ds) = (Module m es is ds',tyEnv')
>   where (ds',tyEnv') = run (unlazyModule m tyEnv ds) tyEnv

\end{verbatim}
We use nested state monad transformers for generating unique names for
the fresh variables replacing lazy patterns and for passing through
the type environment, which is augmented with the types of the new
variables.
\begin{verbatim}

> type UnlazyState a = StateT ValueEnv (StateT Int Id) a

> run :: UnlazyState a -> ValueEnv -> a
> run m tyEnv = runSt (callSt m tyEnv) 1

> unlazyModule :: ModuleIdent -> ValueEnv -> [TopDecl Type]
>              -> UnlazyState ([TopDecl Type],ValueEnv)
> unlazyModule m tyEnv ds = 
>   do
>     dss' <- mapM (unlazyTopDecl m) ds
>     tyEnv' <- fetchSt
>     return (concat dss',tyEnv')

\end{verbatim}
If a pattern declaration uses lazy patterns, its lifted declarations
become part of the same declaration group. Note that since pattern
bindings are evaluated lazily, their patterns are transformed like
lazy patterns.
\begin{verbatim}

> unlazyTopDecl :: ModuleIdent -> TopDecl Type -> UnlazyState [TopDecl Type]
> unlazyTopDecl _ (DataDecl p cx tc tvs cs clss) =
>   return [DataDecl p cx tc tvs cs clss]
> unlazyTopDecl _ (NewtypeDecl p cx tc tvs nc clss) =
>   return [NewtypeDecl p cx tc tvs nc clss]
> unlazyTopDecl _ (TypeDecl p tc tvs ty) = return [TypeDecl p tc tvs ty]
> unlazyTopDecl m (ClassDecl p cx cls tv ds) =
>   liftM (return . ClassDecl p cx cls tv . (tds ++) . concat)
>         (mapM (unlazyDecl m) vds)
>   where (tds,vds) = partition isTypeSig ds
> unlazyTopDecl m (InstanceDecl p cx cls ty ds) =
>   liftM (return . InstanceDecl p cx cls ty . concat) (mapM (unlazyDecl m) ds)
> unlazyTopDecl _ (DefaultDecl p tys) = return [DefaultDecl p tys]
> unlazyTopDecl m (BlockDecl d) = liftM (map BlockDecl) (unlazyDecl m d)
> unlazyTopDecl _ (SplitAnnot p) = return [SplitAnnot p]

> unlazyDecl :: ModuleIdent -> Decl Type -> UnlazyState [Decl Type]
> unlazyDecl m (FunctionDecl p f eqs) =
>   liftM (return . FunctionDecl p f) (mapM (unlazyEquation m) eqs)
> unlazyDecl _ (ForeignDecl p cc s ie f ty) =
>   return [ForeignDecl p cc s ie f ty]
> unlazyDecl m (PatternDecl p t rhs) =
>   do
>     (ds',t') <- liftLazy m p [] (lazyTerm t)
>     rhs' <- unlazyRhs m rhs
>     return (PatternDecl p t' rhs' : ds')
> unlazyDecl _ (FreeDecl p vs) = return [FreeDecl p vs]

> unlazyEquation :: ModuleIdent -> Equation Type
>                -> UnlazyState (Equation Type)
> unlazyEquation m (Equation p (FunLhs f ts) rhs) =
>   do
>     (ds',ts') <- mapAccumM (liftLazy m p) [] (map unlazyTerm ts)
>     rhs' <- unlazyRhs m rhs
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

> liftLazy :: ModuleIdent -> Position -> [Decl Type] -> ConstrTerm Type
>          -> UnlazyState ([Decl Type],ConstrTerm Type)
> liftLazy _ _ ds (LiteralPattern ty l) = return (ds,LiteralPattern ty l)
> liftLazy _ _ ds (VariablePattern ty v) = return (ds,VariablePattern ty v)
> liftLazy m p ds (ConstructorPattern ty c ts) =
>   liftM (apSnd (ConstructorPattern ty c)) (mapAccumM (liftLazy m p) ds ts)
> liftLazy m p ds (AsPattern v t) =
>   case t of
>     LazyPattern t' -> liftM (liftPattern p (typeOf t',v)) (liftLazy m p ds t')
>     _ -> liftM (apSnd (AsPattern v)) (liftLazy m p ds t)
> liftLazy m p ds (LazyPattern t) =
>   liftM2 (liftPattern p) (freshVar m "_#lazy" (typeOf t)) (liftLazy m p ds t)

> liftPattern :: Position -> (a,Ident) -> ([Decl a],ConstrTerm a)
>             -> ([Decl a],ConstrTerm a)
> liftPattern p v (ds,t) =
>   (patDecl p t (uncurry mkVar v) : ds,uncurry VariablePattern v)

\end{verbatim}
Lifted declarations for lazy patterns in lambda expressions and case
alternatives are added to the body of the expression.
\begin{verbatim}

> unlazyRhs :: ModuleIdent -> Rhs Type -> UnlazyState (Rhs Type)
> unlazyRhs m (SimpleRhs p e ds) =
>   do
>     dss' <- mapM (unlazyDecl m) ds
>     e' <- unlazyExpr m e
>     return (SimpleRhs p e' (concat dss'))
> unlazyRhs m (GuardedRhs es ds) =
>   do
>     dss' <- mapM (unlazyDecl m) ds
>     es' <- mapM (unlazyCondExpr m) es
>     return (GuardedRhs es' (concat dss'))

> unlazyCondExpr :: ModuleIdent -> CondExpr Type -> UnlazyState (CondExpr Type)
> unlazyCondExpr m (CondExpr p g e) =
>   liftM2 (CondExpr p) (unlazyExpr m g) (unlazyExpr m e)

> unlazyExpr :: ModuleIdent -> Expression Type -> UnlazyState (Expression Type)
> unlazyExpr _ (Literal ty l) = return (Literal ty l)
> unlazyExpr _ (Variable ty v) = return (Variable ty v)
> unlazyExpr _ (Constructor ty c) = return (Constructor ty c)
> unlazyExpr m (Apply e1 e2) = liftM2 Apply (unlazyExpr m e1) (unlazyExpr m e2)
> unlazyExpr m (Lambda p ts e) =
>   do
>     (ds',ts') <- mapAccumM (liftLazy m p) [] (map unlazyTerm ts)
>     e' <- unlazyExpr m e
>     return (Lambda p ts' (mkLet ds' e'))
> unlazyExpr m (Let ds e) =
>   liftM2 (Let . concat) (mapM (unlazyDecl m) ds) (unlazyExpr m e)
> unlazyExpr m (Case e as) =
>   liftM2 Case (unlazyExpr m e) (mapM (unlazyAlt m) as)
> unlazyExpr m (Fcase e as) =
>   liftM2 Fcase (unlazyExpr m e) (mapM (unlazyAlt m) as)

> unlazyAlt :: ModuleIdent -> Alt Type -> UnlazyState (Alt Type)
> unlazyAlt m (Alt p t rhs) =
>   do
>     (ds',t') <- liftLazy m p [] (unlazyTerm t)
>     rhs' <- unlazyRhs m rhs
>     return (Alt p t' (addDecls ds' rhs'))

\end{verbatim}
Generation of fresh names.
\begin{verbatim}

> freshVar :: ModuleIdent -> String -> Type -> UnlazyState (Type,Ident)
> freshVar m prefix ty =
>   do
>     v <- liftM (mkName prefix) (liftSt (updateSt (1 +)))
>     updateSt_ (bindFun m v 0 (monoType ty))
>     return (ty,v)
>   where mkName pre n = mkIdent (pre ++ show n)

\end{verbatim}
Auxiliary definitions.
\begin{verbatim}

> addDecls :: [Decl a] -> Rhs a -> Rhs a
> addDecls ds (SimpleRhs p e ds') = SimpleRhs p e (ds ++ ds')
> addDecls ds (GuardedRhs es ds') = GuardedRhs es (ds ++ ds')

\end{verbatim}
