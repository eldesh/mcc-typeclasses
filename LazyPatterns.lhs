% -*- LaTeX -*-
% $Id: LazyPatterns.lhs 3256 2016-06-21 07:36:56Z wlux $
%
% Copyright (c) 2001-2016, Wolfgang Lux
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
> import PredefIdent
> import PredefTypes
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

> unlazyDecl :: Decl QualType -> UnlazyState [Decl QualType]
> unlazyDecl (FunctionDecl p ty f eqs) =
>   liftM (return . FunctionDecl p ty f) (mapM unlazyEquation eqs)
> unlazyDecl (ForeignDecl p fi ty f ty') = return [ForeignDecl p fi ty f ty']
> unlazyDecl (PatternDecl p t rhs) =
>   do
>     (ds',t') <- liftLazy p Fcase [] (lazyTerm t)
>     d' <- unlazyRhs rhs >>= normalizePatternDecl p t'
>     return (d' : ds')
> unlazyDecl (FreeDecl p vs) = return [FreeDecl p vs]

> unlazyEquation :: Equation QualType -> UnlazyState (Equation QualType)
> unlazyEquation (Equation p (FunLhs f ts) rhs) =
>   do
>     (ds',ts') <- mapAccumM (liftLazy p Fcase) [] (map unlazyTerm ts)
>     rhs' <- unlazyRhs rhs
>     return (Equation p (FunLhs f ts') (addDecls ds' rhs'))

> normalizePatternDecl :: Position -> ConstrTerm QualType -> Rhs QualType
>                      -> UnlazyState (Decl QualType)
> normalizePatternDecl p t rhs
>   | isVarPattern t = return (PatternDecl p t rhs)
>   | otherwise = normalizedPatternDecl p Fcase t rhs

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

> liftLazy :: Position -> MkCase QualType -> [Decl QualType]
>          -> ConstrTerm QualType
>          -> UnlazyState ([Decl QualType],ConstrTerm QualType)
> liftLazy _ _ ds (LiteralPattern ty l) = return (ds,LiteralPattern ty l)
> liftLazy _ _ ds (VariablePattern ty v) = return (ds,VariablePattern ty v)
> liftLazy p mkCase ds (ConstructorPattern ty c ts) =
>   liftM (apSnd (ConstructorPattern ty c))
>         (mapAccumM (liftLazy p mkCase) ds ts)
> liftLazy p mkCase ds (FunctionPattern ty f ts) =
>   liftM (apSnd (FunctionPattern ty f)) (mapAccumM (liftLazy p mkCase) ds ts)
> liftLazy p mkCase ds (AsPattern v t) =
>   case t of
>     LazyPattern t' -> liftLazy p mkCase ds t' >>= liftPattern p mkCase (ty,v)
>       where ty = qualType (typeOf t')
>     _ -> liftM (apSnd (AsPattern v)) (liftLazy p mkCase ds t)
> liftLazy p mkCase ds (LazyPattern t) =
>   do
>     v <- freshVar "_#lazy" (typeOf t)
>     liftLazy p mkCase ds t >>= liftPattern p mkCase v

> liftPattern :: Position -> MkCase QualType -> (QualType,Ident)
>             -> ([Decl QualType],ConstrTerm QualType)
>             -> UnlazyState ([Decl QualType],ConstrTerm QualType)
> liftPattern p mkCase v (ds,t) =
>   do
>     d <- normalizedPatternDecl p mkCase t (SimpleRhs p (uncurry mkVar v) [])
>     return (d : ds,uncurry VariablePattern v)

\end{verbatim}
Along with the introduction of new pattern declarations for lazy
patterns, we also transform all pattern declarations
$t$~\texttt{=}~$e$ into a normalized form $(x_1,\dots,x_n)$~\texttt{=}
\texttt{fcase}~$e$ \texttt{of} \texttt{\lb}~$\sigma t \rightarrow
(x'_1,\dots,x'_n)$~\texttt{\rb}, where $x_1,\dots,x_n$ are the
variables occurring in $t$, $x'_1,\dots,x'_n$ are fresh variables, and
$\sigma$ is the substitution $\{ x_1 \mapsto x'_1, \dots, x_n \mapsto
x'_n \}$. If $n=0$ or $n=1$, we use the unit constructor and a plain
variable, respectively, instead of tuples. For pattern declarations
introduced for lazy patterns in a rigid case expression we use a
\texttt{case} expression instead of a \texttt{fcase} expression on the
right hand side of the normalized declaration. After simplification,
the compiler will replace the transformed pattern declaration by
individual declarations for those variables from $\{x_1,\dots,x_n\}$
that are used in the scope of the declaration using a space-leak
avoiding transformation of pattern bindings (cf.\ 
Sect.~\ref{sec:pattern-bindings}). The right hand side of a guarded
pattern declaration $t$~\texttt{|} $g_1$~\texttt{=} $e_1$ $\dots$
\texttt{|} $g_n$~\texttt{=} $e_n$ is transformed into an expression of
the form \texttt{fcase} \texttt{()} \texttt{of} \texttt{()}~\texttt{|}
$g_1$~\texttt{->} $e_1$ $\dots$ \texttt{|} $g_n$~\texttt{->} $e_n$ to
perform the transformation.
\begin{verbatim}

> type MkCase a = Expression a -> [Alt a] -> Expression a

> normalizedPatternDecl :: Position -> MkCase QualType -> ConstrTerm QualType
>                       -> Rhs QualType -> UnlazyState (Decl QualType)
> normalizedPatternDecl p mkCase t rhs =
>   do
>     vs' <- mapM (freshVar "_#lazy" . unqualType . fst) vs
>     let t' = rename (zip (map snd vs) (map snd vs')) t
>         t'' = tuplePattern (map (uncurry VariablePattern) vs)
>         e' = tupleExpr (map (uncurry mkVar) vs')
>         rhs' = match (simpleRhs p rhs) [caseAlt p t' e']
>     return (PatternDecl p t'' rhs')
>   where vs = vars t
>         rename _ (LiteralPattern ty l) = LiteralPattern ty l
>         rename vs (VariablePattern ty v) = VariablePattern ty (renameVar vs v)
>         rename vs (ConstructorPattern ty c ts) =
>           ConstructorPattern ty c (map (rename vs) ts)
>         rename vs (FunctionPattern ty f ts) =
>           FunctionPattern ty f (map (rename vs) ts)
>         rename vs (AsPattern v t) = AsPattern (renameVar vs v) (rename vs t)
>         renameVar vs v = maybe v id (lookup v vs)
>         simpleRhs _ (SimpleRhs p e ds) = (p,e,ds)
>         simpleRhs p (GuardedRhs es ds) =
>           (p,Fcase e0 [Alt p t0 (GuardedRhs es [])],ds)
>           where t0 = tuplePattern []; e0 = tupleExpr []
>         match (p,e,ds) as = SimpleRhs p (mkCase e as) ds

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
>     (ds',ts') <- mapAccumM (liftLazy p Fcase) [] (map unlazyTerm ts)
>     e' <- unlazyExpr e
>     return (Lambda p ts' (mkLet ds' e'))
> unlazyExpr (Let ds e) =
>   liftM2 (Let . concat) (mapM unlazyDecl ds) (unlazyExpr e)
> unlazyExpr (Case e as) =
>   liftM2 Case (unlazyExpr e) (mapM (unlazyAlt Case) as)
> unlazyExpr (Fcase e as) =
>   liftM2 Fcase (unlazyExpr e) (mapM (unlazyAlt Fcase) as)

> unlazyAlt :: MkCase QualType -> Alt QualType -> UnlazyState (Alt QualType)
> unlazyAlt mkCase (Alt p t rhs) =
>   do
>     (ds',t') <- liftLazy p mkCase [] (unlazyTerm t)
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

> vars :: ConstrTerm QualType -> [(QualType,Ident)]
> vars (LiteralPattern _ _) = []
> vars (VariablePattern ty v) = [(ty,v) | unRenameIdent v /= anonId]
> vars (ConstructorPattern _ _ ts) = concatMap vars ts
> vars (FunctionPattern _ _ ts) = concatMap vars ts
> vars (AsPattern v t) = (qualType (typeOf t),v) : vars t

> tuplePattern :: [ConstrTerm QualType] -> ConstrTerm QualType
> tuplePattern ts =
>   case ts of
>     [] -> ConstructorPattern qualUnitType qUnitId []
>     [t] -> t
>     _ -> TuplePattern ts

> tupleExpr :: [Expression QualType] -> Expression QualType
> tupleExpr es =
>   case es of
>     [] -> Constructor qualUnitType qUnitId
>     [e] -> e
>     _ -> Tuple es

\end{verbatim}
