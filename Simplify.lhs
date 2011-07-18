% -*- LaTeX -*-
% $Id: Simplify.lhs 3038 2011-07-18 09:15:22Z wlux $
%
% Copyright (c) 2003-2011, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Simplify.lhs}
\section{Optimizing the Desugared Code}\label{sec:simplify}
After desugaring source code and making pattern matching explicit, but
before lifting local declarations, the compiler performs a few simple
optimizations to improve efficiency of the generated code.

Currently, the following optimizations are implemented:
\begin{itemize}
\item Remove unused declarations.
\item Inline simple constants.
\item Compute minimal binding groups.
\item Apply $\eta$-expansion to function definitions when possible.
\item Under certain conditions, inline local function definitions.
\end{itemize}
\begin{verbatim}

> module Simplify(simplify) where
> import Base
> import Combined
> import Curry
> import CurryUtils
> import Env
> import List
> import Monad
> import PredefIdent
> import PredefTypes
> import SCC
> import TrustInfo
> import Types
> import TypeInfo
> import Typing
> import Utils
> import ValueInfo

> type SimplifyState a = ReaderT TCEnv (ReaderT TrustEnv (StateT Int Id)) a
> type InlineEnv = Env Ident (Expression QualType)

> simplify :: TCEnv -> ValueEnv -> TrustEnv -> Module QualType
>          -> (ValueEnv,Module QualType)
> simplify tcEnv tyEnv trEnv m =
>   runSt (callRt (callRt (simplifyModule tyEnv m) tcEnv) trEnv) 1

> simplifyModule :: ValueEnv -> Module QualType
>                -> SimplifyState (ValueEnv,Module QualType)
> simplifyModule tyEnv (Module m es is ds) =
>   do
>     (tyEnv',dss') <- mapAccumM (simplifyTopDecl m) tyEnv ds
>     return (tyEnv',Module m es is (concat dss'))

> simplifyTopDecl :: ModuleIdent -> ValueEnv -> TopDecl QualType
>                 -> SimplifyState (ValueEnv,[TopDecl QualType])
> simplifyTopDecl _ tyEnv (DataDecl p cx tc tvs cs clss) =
>   return (tyEnv,[DataDecl p cx tc tvs cs clss])
> simplifyTopDecl _ tyEnv (NewtypeDecl p cx tc tvs nc clss) =
>   return (tyEnv,[NewtypeDecl p cx tc tvs nc clss])
> simplifyTopDecl _ tyEnv (TypeDecl p tc tvs ty) =
>   return (tyEnv,[TypeDecl p tc tvs ty])
> simplifyTopDecl m tyEnv (ClassDecl p cx cls tv ds) =
>   do
>     dss' <- mapM (simplifyDecl m (bindDecls ds tyEnv) emptyEnv) vds
>     return (tyEnv,[ClassDecl p cx cls tv (tds ++ concatMap snd dss')])
>   where (tds,vds) = partition isTypeSig ds
> simplifyTopDecl m tyEnv (InstanceDecl p cx cls ty ds) =
>   do
>     dss' <- mapM (simplifyDecl m (bindDecls ds tyEnv) emptyEnv) ds
>     return (tyEnv,[InstanceDecl p cx cls ty (concatMap snd dss')])
> simplifyTopDecl _ tyEnv (DefaultDecl p tys) =
>   return (tyEnv,[DefaultDecl p tys])
> simplifyTopDecl m tyEnv (BlockDecl d) =
>   do
>     (tyEnv',ds') <- simplifyDecl m tyEnv emptyEnv d
>     return (tyEnv',map BlockDecl ds')
> simplifyTopDecl _ tyEnv (SplitAnnot p) = return (tyEnv,[SplitAnnot p])

> simplifyDecl :: ModuleIdent -> ValueEnv -> InlineEnv -> Decl QualType
>              -> SimplifyState (ValueEnv,[Decl QualType])
> simplifyDecl m tyEnv env (FunctionDecl p ty f eqs) =
>   do
>     (tyEnv',eqs') <- mapAccumM (flip (simplifyEquation m) env) tyEnv eqs
>     return (tyEnv',[FunctionDecl p ty f eqs'])
> simplifyDecl _ tyEnv _ (ForeignDecl p fi ty f ty') =
>   return (tyEnv,[ForeignDecl p fi ty f ty'])
> simplifyDecl m tyEnv env (PatternDecl p t rhs) =
>   do
>     rhs' <- simplifyRhs m tyEnv env rhs >>= etaExpandRhs tyEnv
>     case (t,rhs') of
>       (VariablePattern ty f,SimpleRhs _ (Lambda _ ts e) _) ->
>         return (changeArity m f (length ts) tyEnv,[funDecl p ty f ts e])
>       (TuplePattern ts,SimpleRhs p' e _) -> return (tyEnv,match p' e)
>         where match _ (Variable _ v) =
>                 [patDecl p t (Variable (qualType (typeOf t)) v) | t <- ts]
>               match _ (Tuple es) = zipWith (patDecl p) ts es
>               match p' (Let ds e) = ds ++ match p' e
>               match p' e@(Case _ _) = [PatternDecl p t (SimpleRhs p' e [])]
>               match p' e@(Fcase _ _) = [PatternDecl p t (SimpleRhs p' e [])]
>       _ -> return (tyEnv,[PatternDecl p t rhs'])
> simplifyDecl _ tyEnv _ (FreeDecl p vs) = return (tyEnv,[FreeDecl p vs])

> simplifyEquation :: ModuleIdent -> ValueEnv -> InlineEnv -> Equation QualType
>                  -> SimplifyState (ValueEnv,Equation QualType)
> simplifyEquation m tyEnv env (Equation p lhs rhs) =
>   do
>     rhs' <- simplifyRhs m tyEnv' env rhs >>= etaExpandRhs tyEnv'
>     case (simplifyLhs (qfv m rhs') lhs,rhs') of
>       (FunLhs f ts,SimpleRhs p' (Lambda _ ts' e') _) ->
>         return (changeArity m f (length ts + length ts') tyEnv,
>                 Equation p (FunLhs f (ts ++ ts')) (SimpleRhs p' e' []))
>       (lhs',_) -> return (tyEnv,Equation p lhs' rhs')
>   where tyEnv' = bindLhs lhs tyEnv

> simplifyLhs :: [Ident] -> Lhs a -> Lhs a
> simplifyLhs fvs (FunLhs f ts) = FunLhs f (map (simplifyPattern fvs) ts)

> simplifyRhs :: ModuleIdent -> ValueEnv -> InlineEnv -> Rhs QualType
>             -> SimplifyState (Rhs QualType)
> simplifyRhs m tyEnv env (SimpleRhs p e _) =
>   do
>     e' <- simplifyApp p e [] >>= simplifyExpr m tyEnv env
>     return (SimpleRhs p e' [])

\end{verbatim}
\label{eta-expansion}
After transforming the right hand side of a variable declaration and
the body of a function equation\footnote{Recall that after making
  pattern matching explicit each function is defined by exactly one
  equation.}, respectively, the compiler tries to $\eta$-expand the
definition. Using $\eta$-expanded definitions has the advantage that
the compiler can avoid intermediate lazy applications. For instance,
if the \texttt{map} function were defined as follows
\begin{verbatim}
  map f = foldr (\x -> (f x :)) []
\end{verbatim}
the compiler would compile the application \texttt{map (1+) [0..]}
into an expression that is equivalent to
\begin{verbatim}
  let a1 = map (1+) in a1 [0..]
\end{verbatim}
whereas the $\eta$-expanded version of \texttt{map} could be applied
directly to both arguments.

However, one must be careful with $\eta$-expansion because it can have
an effect on sharing and thus can change the semantics of a program.
For instance, consider the functions
\begin{verbatim}
  f1 g h    = filter (g ? h)
  f2 g h xs = filter (g ? h) xs
\end{verbatim}
and the goals \texttt{map (f1 even odd) [[0,1], [2,3]]} and
\texttt{map (f2 even odd) [[0,1], [2,3]]}. The first of these has only
two solutions, namely \texttt{[[0],[2]]} and \texttt{[[1],[3]]},
because the expression \texttt{(even ?\ odd)} is evaluated only once,
whereas the second has four solutions because the expression
\texttt{(even ?\ odd)} is evaluated independently for the two argument
lists \texttt{[0,1]} and \texttt{[2,3]}.

Obviously, $\eta$-expansion of an equation \texttt{$f\,t_1\dots t_n$ =
  $e$} is safe if the two expressions \texttt{($f\,x_1\dots x_n$,
  $f\,x_1\dots x_n$)} and \texttt{let a = $f\,x_1\dots x_n$ in (a,a)}
are equivalent. In order to find a safe approximation of definitions
for which this property holds, the distinction between expansive and
non-expansive expressions is useful again, which was introduced to
identify let-bound variables for which polymorphic generalization is
safe (see p.~\pageref{non-expansive} in Sect.~\ref{non-expansive}). An
expression is non-expansive if it is either
\begin{itemize}
\item a literal,
\item a variable,
\item an application of a constructor with arity $n$ to at most $n$
  non-expansive expressions,
\item an application of a function or $\lambda$-abstraction with arity
  $n$ to at most $n-1$ non-expansive expressions,
\item an application of a $\lambda$-abstraction with arity $n$ to $n$
  or more non-expansive expressions and the application of the
  $\lambda$-abstraction's body to the excess arguments is
  non-expansive, or
\item a let expression whose body is a non-expansive expression and
  whose local declarations are either function declarations or
  variable declarations of the form \texttt{$x$=$e$} where $e$ is a
  non-expansive expression.
\end{itemize}
A function or variable definition can be $\eta$-expanded safely if its
body is a non-expansive expression.
\begin{verbatim}

> etaExpandRhs :: ValueEnv -> Rhs QualType -> SimplifyState (Rhs QualType)
> etaExpandRhs tyEnv rhs@(SimpleRhs p e _) =
>   do
>     (ts',e') <- etaExpand tyEnv e
>     return (if null ts' then rhs else SimpleRhs p (Lambda p ts' e') [])

> etaExpand :: ValueEnv -> Expression QualType
>           -> SimplifyState ([ConstrTerm QualType],Expression QualType)
> etaExpand tyEnv e =
>   do
>     tcEnv <- envRt
>     etaExpr tcEnv tyEnv e

> etaExpr :: TCEnv -> ValueEnv -> Expression QualType
>         -> SimplifyState ([ConstrTerm QualType],Expression QualType)
> etaExpr _ _ (Lambda _ ts e) = return (ts,e)
> etaExpr tcEnv tyEnv e
>   | isNonExpansive tyEnv 0 e && not (null tys) =
>       do
>         vs <- mapM (freshVar "_#eta") tys
>         return (map (uncurry VariablePattern) vs,
>                 etaApply e' (map (uncurry mkVar) vs))
>   | otherwise = return ([],e)
>   where n = exprArity tyEnv e
>         (ty',e') = expandTypeAnnot tcEnv n e
>         tys = take n (arrowArgs ty')
>         etaApply e es =
>           case e of
>             Let ds e -> Let ds (etaApply e es)
>             _ -> apply e es

> isNonExpansive :: ValueEnv -> Int -> Expression QualType -> Bool
> isNonExpansive _ _ (Literal _ _) = True
> isNonExpansive tyEnv n (Variable _ x)
>   | not (isQualified x) = n == 0 || n < arity x tyEnv
>   | otherwise = n < arity x tyEnv
> isNonExpansive _ _ (Constructor _ _) = True
> isNonExpansive tyEnv n (Tuple es) = n == 0 && all (isNonExpansive tyEnv 0) es
> isNonExpansive tyEnv n (Apply e1 e2) =
>   isNonExpansive tyEnv (n + 1) e1 && isNonExpansive tyEnv 0 e2
> isNonExpansive tyEnv n (Lambda _ ts e) =
>   n' < 0 || isNonExpansive (bindTerms ts tyEnv) n' e
>   where n' = n - length ts
> isNonExpansive tyEnv n (Let ds e) =
>   all (isNonExpansiveDecl tyEnv') ds && isNonExpansive tyEnv' n e
>   where tyEnv' = bindDecls ds tyEnv
> isNonExpansive _ _ (Case _ _) = False
> isNonExpansive _ _ (Fcase _ _) = False

> isNonExpansiveDecl :: ValueEnv -> Decl QualType -> Bool
> isNonExpansiveDecl _ (FunctionDecl _ _ _ _) = True
> isNonExpansiveDecl _ (ForeignDecl _ _ _ _ _) = True
> isNonExpansiveDecl tyEnv (PatternDecl _ _ (SimpleRhs _ e _)) =
>   isNonExpansive tyEnv 0 e
> isNonExpansiveDecl _ (FreeDecl _ _) = False

> exprArity :: ValueEnv -> Expression QualType -> Int
> exprArity _ (Literal _ _) = 0
> exprArity tyEnv (Variable _ x) = arity x tyEnv
> exprArity tyEnv (Constructor _ c) = arity c tyEnv
> exprArity _ (Tuple _) = 0
> exprArity tyEnv (Apply e _) = exprArity tyEnv e - 1
> exprArity _ (Lambda _ ts _) = length ts
> exprArity tyEnv (Let ds e) = exprArity (bindDecls ds tyEnv) e
> exprArity _ (Case _ _) = 0
> exprArity _ (Fcase _ _) = 0

\end{verbatim}
Since newtype constructors have been removed already, the compiler may
perform $\eta$-expansion even across newtypes. For instance, given the
source definitions
\begin{verbatim}
  newtype ST s a = ST (s -> (a,s))
  doneST     = returnST ()
  returnST x = ST (\s -> (x,s))
\end{verbatim}
the functions \texttt{doneST} and \texttt{returnST} are expanded into
functions with arity one and two, respectively. In order to determine
the types of the variables added by $\eta$-expansion in such cases,
the compiler must expand the type annotations as well. In the example,
the type annotation of function \texttt{returnST} in the definition of
\texttt{doneST} is changed from $() \rightarrow
\texttt{ST}\,\alpha_1\,()$ to $() \rightarrow \alpha_1 \rightarrow
((),\alpha_1)$. This is implemented in function
\texttt{expandTypeAnnot}, which tries to expand the type annotations
of $e$'s root such that the expression has (at least) arity $n$. Note
that this may fail when the newtype's definition is not visible in the
current module.
\begin{verbatim}

> expandTypeAnnot :: TCEnv -> Int -> Expression QualType
>                 -> (Type,Expression QualType)
> expandTypeAnnot tcEnv n e
>   | n <= arrowArity ty = (ty,e)
>   | otherwise = (ty',fixType ty' e)
>   where ty = typeOf e
>         ty' = etaType tcEnv n ty

> fixType :: Type -> Expression QualType -> Expression QualType
> fixType ty (Literal _ l) = Literal (qualType ty) l
> fixType ty (Variable _ v) = Variable (qualType ty) v
> fixType ty (Constructor _ c) = Constructor (qualType ty) c
> fixType _ (Tuple es) = Tuple es
> fixType ty (Apply e1 e2) = Apply (fixType (TypeArrow (typeOf e2) ty) e1) e2
> fixType ty (Lambda p ts e) = Lambda p ts (fixType (foldr match ty ts) e)
>   where match _ (TypeArrow _ ty) = ty
> fixType ty (Let ds e) = Let ds (fixType ty e)
> fixType ty (Case e as) = Case e (map (fixTypeAlt ty) as)
> fixType ty (Fcase e as) = Fcase e (map (fixTypeAlt ty) as)

> fixTypeAlt :: Type -> Alt QualType -> Alt QualType
> fixTypeAlt ty (Alt p t rhs) = Alt p t (fixTypeRhs ty rhs)

> fixTypeRhs :: Type -> Rhs QualType -> Rhs QualType
> fixTypeRhs ty (SimpleRhs p e _) = SimpleRhs p (fixType ty e) []

\end{verbatim}
Before other optimizations are applied to expressions, the simplifier
first transforms applications of let and (f)case expressions by
pushing the application down into the body of let expressions and into
the alternatives of (f)case expressions, respectively. In order to
avoid code duplication, arguments that are pushed into the
alternatives of a (f)case expression by this transformation are bound
to local variables (unless there is only one alternative). If these
arguments are just simple variables or literal constants, the
optimizations performed in \texttt{simplifyExpr} below will substitute
these values and the let declarations will be removed.

\ToDo{Optimize (saturated) applications of $\lambda$-abstractions by
  performing a compile time $\beta$-reduction.}
\begin{verbatim}

> simplifyApp :: Position -> Expression QualType -> [Expression QualType]
>             -> SimplifyState (Expression QualType)
> simplifyApp _ (Literal ty l) _ = return (Literal ty l)
> simplifyApp _ (Variable ty v) es = return (apply (Variable ty v) es)
> simplifyApp _ (Constructor ty c) es = return (apply (Constructor ty c) es)
> simplifyApp p (Tuple es) _ = liftM Tuple (mapM (flip (simplifyApp p) []) es)
> simplifyApp p (Apply e1 e2) es =
>   do
>     e2' <- simplifyApp p e2 []
>     simplifyApp p e1 (e2':es)
> simplifyApp _ (Lambda p ts e) es = return (apply (Lambda p ts e) es)
> simplifyApp p (Let ds e) es = liftM (Let ds) (simplifyApp p e es)
> simplifyApp p (Case e as) es =
>   do
>     e' <- simplifyApp p e []
>     mkCase p (Case e') es as
> simplifyApp p (Fcase e as) es =
>   do
>     e' <- simplifyApp p e []
>     mkCase p (Fcase e') es as

> mkCase :: Position -> ([Alt QualType] -> Expression QualType)
>        -> [Expression QualType] -> [Alt QualType]
>        -> SimplifyState (Expression QualType)
> mkCase p f es as
>   | length as == 1 = return (f (map (applyToAlt es) as))
>   | otherwise =
>       do
>         vs <- mapM (freshVar "_#arg" . typeOf) es
>         let es' = map (uncurry mkVar) vs
>         return (foldr2 mkLet (f (map (applyToAlt es') as)) vs es)
>   where applyToAlt es (Alt p t rhs) = Alt p t (applyToRhs es rhs)
>         applyToRhs es (SimpleRhs p e _) = SimpleRhs p (apply e es) []
>         mkLet (ty,v) e1 e2 = Let [varDecl p ty v e1] e2

\end{verbatim}
Variables that are bound to (simple) constants and aliases to other
variables are substituted. In terms of conventional compiler
technology, these optimizations correspond to constant folding and
copy propagation, respectively. The transformation is applied
recursively to a substituted variable in order to handle chains of
variable definitions. Note that the compiler carefully updates the
type annotations of the inlined expression. This is necessary to
preserve soundness of the annotations when inlining a variable with a
polymorphic type because in that case each use of the variable is
annotated with fresh type variables that are unrelated to the type
variables used on the right hand side of the variable's definition. In
addition, newtype constructors in the result of the substituted
expression's type are expanded as far as necessary to ensure that the
annotated type has the same arity before and after the substitution.

\ToDo{Apply the type substitution only when necessary, i.e., when the
  inlined variable has a polymorphic type.}

The bindings of a let expression are sorted topologically to split
them into minimal binding groups. In addition, local declarations
occurring on the right hand side of variable and pattern declarations
are lifted into the enclosing binding group using the equivalence
(modulo $\alpha$-conversion) of \texttt{let} $x$~=~\texttt{let}
\emph{decls} \texttt{in} $e_1$ \texttt{in} $e_2$ and \texttt{let}
\emph{decls}\texttt{;} $x$~=~$e_1$ \texttt{in} $e_2$.  This
transformation avoids the creation of some redundant lifted functions
in later phases of the compiler.
\begin{verbatim}

> simplifyExpr :: ModuleIdent -> ValueEnv -> InlineEnv -> Expression QualType
>              -> SimplifyState (Expression QualType)
> simplifyExpr _ _ _ (Literal ty l) = return (Literal ty l)
> simplifyExpr m tyEnv env (Variable ty v)
>   | isQualified v = return (Variable ty v)
>   | otherwise =
>       do
>         tcEnv <- envRt
>         maybe (return (Variable ty v))
>               (simplifyExpr m tyEnv env . substExpr tcEnv (unqualType ty))
>               (lookupEnv (unqualify v) env)
>   where substExpr tcEnv ty =
>           snd . expandTypeAnnot tcEnv (arrowArity ty) . withType tcEnv ty
> simplifyExpr _ _ _ (Constructor ty c) = return (Constructor ty c)
> simplifyExpr m tyEnv env (Tuple es) =
>   liftM Tuple (mapM (simplifyExpr m tyEnv env) es)
> simplifyExpr m tyEnv env (Apply e1 e2) =
>   do
>     e1' <- simplifyExpr m tyEnv env e1
>     e2' <- simplifyExpr m tyEnv env e2
>     return (Apply e1' e2')
> simplifyExpr m tyEnv env (Lambda p ts e) =
>   do
>     e' <- simplifyApp p e [] >>= simplifyExpr m tyEnv' env
>     (ts',e'') <- etaExpand tyEnv' e'
>     let ts'' = map (simplifyPattern (qfv m (Lambda p ts' e''))) ts ++ ts'
>     return (etaReduce m tyEnv' p ts'' e'')
>   where tyEnv' = bindTerms ts tyEnv
> simplifyExpr m tyEnv env (Let ds e) =
>   simplifyLet m tyEnv env (scc bv (qfv m) (foldr hoistDecls [] ds)) e
> simplifyExpr m tyEnv env (Case e as) =
>   do
>     e' <- simplifyExpr m tyEnv env e
>     maybe (liftM (Case e') (mapM (simplifyAlt m tyEnv env) as))
>           (simplifyExpr m tyEnv env)
>           (simplifyMatch e' as)
> simplifyExpr m tyEnv env (Fcase e as) =
>   do
>     e' <- simplifyExpr m tyEnv env e
>     maybe (liftM (Fcase e') (mapM (simplifyAlt m tyEnv env) as))
>           (simplifyExpr m tyEnv env)
>           (simplifyMatch e' as)

> simplifyAlt :: ModuleIdent -> ValueEnv -> InlineEnv -> Alt QualType
>             -> SimplifyState (Alt QualType)
> simplifyAlt m tyEnv env (Alt p t rhs) =
>   do
>     rhs' <- simplifyRhs m (bindTerm t tyEnv) env rhs
>     return (Alt p (simplifyPattern (qfv m rhs') t) rhs')

> simplifyPattern :: [Ident] -> ConstrTerm a -> ConstrTerm a
> simplifyPattern _ (LiteralPattern a l) = LiteralPattern a l
> simplifyPattern _ (VariablePattern a v) = VariablePattern a v
> simplifyPattern fvs (ConstructorPattern a c ts) =
>   ConstructorPattern a c (map (simplifyPattern fvs) ts)
> simplifyPattern fvs (AsPattern v t) =
>   (if v `elem` fvs then AsPattern v else id) (simplifyPattern fvs t)

> hoistDecls :: Decl a -> [Decl a] -> [Decl a]
> hoistDecls (PatternDecl p t (SimpleRhs p' (Let ds e) _)) ds' =
>   foldr hoistDecls ds' (PatternDecl p t (SimpleRhs p' e []) : ds)
> hoistDecls d ds = d : ds

\end{verbatim}
The declaration groups of a let expression are first processed from
outside to inside, simplifying the right hand sides and collecting
inlineable expressions on the fly. At present, only simple constants
and aliases to other variables are inlined. In addition, for function
definitions of the form $f\,x_{m+1}\dots x_n = g\,e_1\dots
e_m\,x_{m+1} \dots x_n$ where $g$ is a function or constructor whose
arity is greater than or equal to $n$ and where $e_1,\dots,e_m$ are
either simple constants or free variables of $f$, the application
$g\,e_1\dots e_m$ is inlined in place of $f$.

A constant is considered simple if it is either a literal, a
constructor, or a non-nullary function. Since it is not possible to
define nullary functions in a local declaration groups in Curry, an
unqualified name here always refers to either a variable or a
non-nullary function. Applications of constructors and partial
applications of functions to at least one argument are not inlined to
avoid code duplication (for the allocation of the terms). In order to
prevent non-termination, no inlining is performed for entities defined
in recursive binding groups.

With the list of inlineable expressions, the body of the let is
simplified and then the declaration groups are processed from inside
to outside to construct the simplified, nested let expression. In
doing so unused bindings are discarded and pattern bindings are
restricted to those variables actually used in the scope of the
declaration. In addition, minimal binding groups are recomputed in
case compile time matching of pattern bindings did introduce new
variable declarations (see \texttt{simplifyDecl} above).
\begin{verbatim}

> simplifyLet :: ModuleIdent -> ValueEnv -> InlineEnv -> [[Decl QualType]]
>             -> Expression QualType -> SimplifyState (Expression QualType)
> simplifyLet m tyEnv env [] e = simplifyExpr m tyEnv env e
> simplifyLet m tyEnv env (ds:dss) e =
>   do
>     (tyEnv',dss') <-
>       mapAccumM (flip (simplifyDecl m) env) (bindDecls ds tyEnv) ds
>     tcEnv <- envRt
>     trEnv <- liftRt envRt
>     let dss'' = scc bv (qfv m) (concat dss')
>     e' <-
>       simplifyLet m tyEnv' (foldr (inlineVars m tyEnv' trEnv) env dss'') dss e
>     return (snd (foldr (mkSimplLet m tcEnv) (qfv m e',e') dss''))

> inlineVars :: ModuleIdent -> ValueEnv -> TrustEnv -> [Decl QualType]
>            -> InlineEnv -> InlineEnv
> inlineVars m tyEnv trEnv
>            [FunctionDecl _ _ f [Equation p (FunLhs _ ts) (SimpleRhs _ e _)]]
>            env
>   | f `notElem` qfv m e && trustedFun trEnv f =
>       case etaReduce m (bindTerms ts tyEnv) p ts e of
>         Lambda _ _ _ -> env
>         e' -> bindEnv f e' env
> inlineVars m tyEnv _
>            [PatternDecl _ (VariablePattern _ v) (SimpleRhs _ e _)]
>            env
>   | canInline tyEnv e && v `notElem` qfv m e = bindEnv v e env
> inlineVars _ _ _ _ env = env

> etaReduce :: ModuleIdent -> ValueEnv -> Position -> [ConstrTerm QualType]
>           -> Expression QualType -> Expression QualType
> etaReduce m tyEnv p ts e
>   | all isVarPattern ts && funArity e' >= n && length ts <= n &&
>     all (canInline tyEnv) es' && map (uncurry mkVar) vs == es'' &&
>     all ((`notElem` qfv m e'') . snd) vs = e''
>   | otherwise = Lambda p ts e
>   where n = length es
>         vs = [(ty,v) | VariablePattern ty v <- ts]
>         (e',es) = unapply e []
>         (es',es'') = splitAt (n - length ts) es
>         e'' = apply e' es'
>         funArity (Variable _ v) = arity v tyEnv
>         funArity (Constructor _ c) = arity c tyEnv
>         funArity _ = -1

> canInline :: ValueEnv -> Expression a -> Bool
> canInline _ (Literal _ _) = True
> canInline _ (Constructor _ _) = True
> canInline tyEnv (Variable _ v) = not (isQualified v) || arity v tyEnv > 0
> canInline _ _ = False

> mkSimplLet :: ModuleIdent -> TCEnv -> [Decl QualType]
>            -> ([Ident],Expression QualType) -> ([Ident],Expression QualType)
> mkSimplLet m _ [FreeDecl p vs] (fvs,e)
>   | null vs' = (fvs,e)
>   | otherwise = (fvs',Let [FreeDecl p vs'] e)
>   where vs' = [FreeVar ty v | FreeVar ty v <- vs, v `elem` fvs]
>         fvs' = filter (`notElem` bv vs) fvs
> mkSimplLet m tcEnv [PatternDecl _ (VariablePattern _ v) (SimpleRhs _ e _)]
>       (_,Variable ty' v')
>   | v' == qualify v && v `notElem` fvs =
>       (fvs,withType tcEnv (unqualType ty') e)
>   where fvs = qfv m e
> mkSimplLet m _ ds (fvs,e)
>   | null (filter (`elem` fvs) bvs) = (fvs,e)
>   | otherwise =
>       (filter (`notElem` bvs) fvs',Let (map (simplifyPatternDecl fvs') ds) e)
>   where fvs' = qfv m ds ++ fvs
>         bvs = bv ds

> simplifyPatternDecl :: [Ident] -> Decl QualType -> Decl QualType
> simplifyPatternDecl fvs (PatternDecl p (TuplePattern ts) rhs) =
>   PatternDecl p (tuplePattern (filterUsed ts)) (filterRhs rhs)
>   where bs = [v `elem` fvs | VariablePattern ty v <- ts]
>         filterUsed xs = [x | (b,x) <- zip bs xs, b]
>         filterRhs (SimpleRhs p e _) = SimpleRhs p (filterBody e) []
>         filterBody (Variable _ v) =
>           tupleExpr (filterUsed [Variable ty v | VariablePattern ty _ <- ts])
>         filterBody (Tuple es) = tupleExpr (filterUsed es)
>         filterBody (Case e [Alt p t rhs]) = Case e [Alt p t (filterRhs rhs)]
>         filterBody (Fcase e [Alt p t rhs]) =
>           Fcase e [Alt p t (filterRhs rhs)]
>         filterBody (Let ds e) = Let ds (filterBody e)
> simplifyPatternDecl _ d = d

\end{verbatim}
When the scrutinized expression of a $($f$)$case expression is a
literal or a constructor application, the compiler can perform the
pattern matching already at compile time and simplify the case
expression to the right hand side of the matching alternative or to
\texttt{Prelude.failed} if no alternative matches. When a case
expression collapses to a matching alternative, the pattern variables
are bound to the matching (sub)terms of the scrutinized expression. We
have to be careful with as-patterns to avoid losing sharing by code
duplication. For instance, the expression
\begin{verbatim}
  case (0?1) : undefined of
    l@(x:_) -> (x,l)
\end{verbatim}
must be transformed into
\begin{verbatim}
  let { x = 0?1; xs = undefined } in
  let { l = x:xs } in
  (x,l)
\end{verbatim}
I.e., variables defined in an as-pattern must be bound to a fresh
term, which is constructed from the matched pattern, instead of
binding them to the scrutinized expression. The risk of code
duplication is also the reason why the compiler currently does not
inline variables bound to constructor applications. This would be safe
in general only when the program were transformed into a normalized
form where the arguments of all applications would be variables.
\begin{verbatim}

> simplifyMatch :: Expression QualType -> [Alt QualType]
>               -> Maybe (Expression QualType)
> simplifyMatch (Let ds e) = fmap (Let ds) . simplifyMatch e
> simplifyMatch e =
>   case unapply e [] of
>     (Literal ty l,_) -> Just . match (Left (ty,l))
>     (Constructor ty c,es) -> Just . match (Right (ty,c,es))
>     (_,_) -> const Nothing

> unapply :: Expression a -> [Expression a] -> (Expression a,[Expression a])
> unapply (Literal ty l) es = (Literal ty l,es)
> unapply (Variable ty v) es = (Variable ty v,es)
> unapply (Constructor ty c) es = (Constructor ty c,es)
> unapply (Tuple es') es = (Tuple es',es)
> unapply (Apply e1 e2) es = unapply e1 (e2:es)
> unapply (Lambda p ts e) es = (Lambda p ts e,es)
> unapply (Let ds e) es = (Let ds e,es)
> unapply (Case e as) es = (Case e as,es)
> unapply (Fcase e as) es = (Fcase e as,es)

> match :: Either (QualType,Literal) (QualType,QualIdent,[Expression QualType])
>       -> [Alt QualType] -> Expression QualType
> match e as =
>   head ([expr p t rhs | Alt p t rhs <- as, t `matches` e] ++
>         [prelFailed (qualType (typeOf (Case (matchExpr e) as)))])
>   where expr p t (SimpleRhs _ e' _) = bindPattern p e t e'

> matches :: ConstrTerm a -> Either (a,Literal) (a,QualIdent,[Expression a])
>         -> Bool
> matches (LiteralPattern _ l1) (Left (_,l2)) = l1 == l2
> matches (ConstructorPattern _ c1 _) (Right (_,c2,_)) = c1 == c2
> matches (VariablePattern _ _) _ = True
> matches (AsPattern _ t) e = matches t e

> matchExpr :: Either (a,Literal) (a,QualIdent,[Expression a]) -> Expression a
> matchExpr (Left (ty,l)) = Literal ty l
> matchExpr (Right (ty,c,es)) = apply (Constructor ty c) es

> bindPattern :: Position
>             -> Either (QualType,Literal)
>                       (QualType,QualIdent,[Expression QualType])
>             -> ConstrTerm QualType -> Expression QualType
>             -> Expression QualType
> bindPattern _ (Left _) (LiteralPattern _ _) e' = e'
> bindPattern p (Right (_,_,es)) (ConstructorPattern _ _ ts) e' =
>   foldr Let e' [zipWith (patDecl p) ts es]
> bindPattern p e (VariablePattern ty v) e' =
>   Let [varDecl p ty v (matchExpr e)] e'
> bindPattern p e (AsPattern v t) e' = bindPattern p e t (Let [bindAs p v t] e')

> bindAs :: Position -> Ident -> ConstrTerm QualType -> Decl QualType
> bindAs p v (LiteralPattern ty l) = varDecl p ty v (Literal ty l)
> bindAs p v (VariablePattern ty v') = varDecl p ty v (mkVar ty v')
> bindAs p v (ConstructorPattern ty c ts) =
>   varDecl p ty v (apply (Constructor (toExprType ty ts) c) (map toExpr ts))
>   where toExpr (VariablePattern ty v) = mkVar ty v
>         toExprType ty ts =
>           qualType (foldr (TypeArrow . typeOf) (unqualType ty) ts)
> bindAs p v (AsPattern v' t') = varDecl p ty v (mkVar ty v')
>   where ty = qualType (typeOf t')

> prelFailed :: a -> Expression a
> prelFailed ty = Variable ty (qualifyWith preludeMIdent (mkIdent "failed"))

\end{verbatim}
Generation of fresh names.
\begin{verbatim}

> freshVar :: String -> Type -> SimplifyState (QualType,Ident)
> freshVar prefix ty =
>   do
>     v <- liftM mkName (liftRt (liftRt (updateSt (1 +))))
>     return (qualType ty,v)
>   where mkName n = renameIdent (mkIdent (prefix ++ show n)) n

\end{verbatim}
Auxiliary functions.
\begin{verbatim}

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
