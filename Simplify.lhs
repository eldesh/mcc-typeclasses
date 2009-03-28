% -*- LaTeX -*-
% $Id: Simplify.lhs 2778 2009-03-28 09:10:58Z wlux $
%
% Copyright (c) 2003-2009, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Simplify.lhs}
\section{Optimizing the Desugared Code}\label{sec:simplify}
After desugaring the source code, but before lifting local
declarations, the compiler performs a few simple optimizations to
improve efficiency of the generated code. In addition, the optimizer
replaces pattern bindings with simple variable bindings and selector
functions.

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
> import Monad
> import PredefIdent
> import SCC
> import TrustInfo
> import Types
> import Typing
> import Utils
> import ValueInfo

> type SimplifyState a =
>   StateT ValueEnv (ReaderT NewtypeEnv (ReaderT TrustEnv (StateT Int Id))) a
> type InlineEnv = Env Ident (Expression Type)

> simplify :: ValueEnv -> TrustEnv -> Module Type -> (Module Type,ValueEnv)
> simplify tyEnv trEnv m =
>   runSt (callRt (callRt (callSt (simplifyModule m) tyEnv) nEnv) trEnv) 1
>   where nEnv = newtypeEnv tyEnv

> simplifyModule :: Module Type -> SimplifyState (Module Type,ValueEnv)
> simplifyModule (Module m es is ds) =
>   do
>     ds' <- mapM (simplifyTopDecl m) ds
>     tyEnv <- fetchSt
>     return (Module m es is ds',tyEnv)

> simplifyTopDecl :: ModuleIdent -> TopDecl Type -> SimplifyState (TopDecl Type)
> simplifyTopDecl _ (DataDecl p cx tc tvs cs clss) =
>   return (DataDecl p cx tc tvs cs clss)
> simplifyTopDecl _ (NewtypeDecl p cx tc tvs nc clss) =
>   return (NewtypeDecl p cx tc tvs nc clss)
> simplifyTopDecl _ (TypeDecl p tc tvs ty) = return (TypeDecl p tc tvs ty)
> simplifyTopDecl m (ClassDecl p cx cls tv ds) =
>   liftM (ClassDecl p cx cls tv) (mapM (simplifyDecl m emptyEnv) ds)
> simplifyTopDecl m (InstanceDecl p cx cls ty ds) =
>   liftM (InstanceDecl p cx cls ty) (mapM (simplifyDecl m emptyEnv) ds)
> simplifyTopDecl _ (DefaultDecl p tys) = return (DefaultDecl p tys)
> simplifyTopDecl m (BlockDecl d) =
>   liftM BlockDecl (simplifyDecl m emptyEnv d)

> simplifyDecl :: ModuleIdent -> InlineEnv -> Decl Type
>              -> SimplifyState (Decl Type)
> simplifyDecl _ _ (TypeSig p fs ty) = return (TypeSig p fs ty)
> simplifyDecl m env (FunctionDecl p f eqs) =
>   liftM (FunctionDecl p f) (mapM (simplifyEquation m env) eqs >>= etaExpand m)
> simplifyDecl _ _ (ForeignDecl p cc s ie f ty) =
>   return (ForeignDecl p cc s ie f ty)
> simplifyDecl m env (PatternDecl p t rhs) =
>   do
>     rhs' <- simplifyRhs m env rhs
>     case rhs' of
>       SimpleRhs _ (Lambda _ ts e) _ ->
>         do
>           updateSt_ (changeArity m f (length ts))
>           return (funDecl p f ts e)
>         where VariablePattern _ f = t
>       _ -> return (PatternDecl p t rhs')
> simplifyDecl _ _ (FreeDecl p vs) = return (FreeDecl p vs)

> simplifyEquation :: ModuleIdent -> InlineEnv -> Equation Type
>                  -> SimplifyState (Equation Type)
> simplifyEquation m env (Equation p lhs rhs) =
>   liftM (Equation p lhs) (simplifyRhs m env rhs)

> simplifyRhs :: ModuleIdent -> InlineEnv -> Rhs Type
>             -> SimplifyState (Rhs Type)
> simplifyRhs m env (SimpleRhs p e _) =
>   do
>     e' <- simplifyApp m p e [] >>= simplifyExpr m env
>     return (SimpleRhs p e' [])

\end{verbatim}
\label{eta-expansion}
After transforming the bodies of each equation defining a function,
the compiler tries to $\eta$-expand the definition. Using
$\eta$-expanded definitions has the advantage that the compiler can
avoid intermediate lazy applications. For instance, if the
\texttt{map} function were defined as follows
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
non-expansive expressions is useful again, which was introduced in
order to identify let-bound variables for which polymorphic
generalization is safe (see p.~\pageref{non-expansive} in
Sect.~\ref{non-expansive}). An expression is non-expansive if it is
either
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
A function definition then can be $\eta$-expanded safely if it has
only a single equation whose body is a non-expansive expression.
\begin{verbatim}

> etaExpand :: ModuleIdent -> [Equation Type] -> SimplifyState [Equation Type]
> etaExpand m [eq] =
>   do
>     tyEnv <- fetchSt
>     nEnv <- liftSt envRt
>     etaEquation m tyEnv nEnv eq
> etaExpand _ eqs = return eqs

> etaEquation :: ModuleIdent -> ValueEnv -> NewtypeEnv -> Equation Type
>             -> SimplifyState [Equation Type]
> etaEquation m tyEnv nEnv (Equation p1 (FunLhs f ts) (SimpleRhs p2 e _)) =
>   do
>     (ts',e') <- etaExpr m tyEnv nEnv e
>     unless (null ts') (updateSt_ (changeArity m f (length ts + length ts')))
>     return [Equation p1 (FunLhs f (ts ++ ts')) (SimpleRhs p2 e' [])]

> etaExpr :: ModuleIdent -> ValueEnv -> NewtypeEnv -> Expression Type
>         -> SimplifyState ([ConstrTerm Type],Expression Type)
> etaExpr _ _ _ (Lambda _ ts e) = return (ts,e)
> etaExpr m tyEnv nEnv e
>   | isNonExpansive tyEnv 0 e && not (null tys) =
>       do
>         vs <- mapM (freshVar m etaId) tys
>         return (map (uncurry VariablePattern) vs,
>                 etaApply e' (map (uncurry mkVar) vs))
>   | otherwise = return ([],e)
>   where n = exprArity tyEnv e
>         (ty',e') = expandTypeAnnot nEnv n e
>         tys = take n (arrowArgs ty')
>         etaId n = mkIdent ("_#eta" ++ show n)
>         etaApply e es =
>           case e of
>             Let ds e -> Let ds (etaApply e es)
>             _ -> apply e es

> isNonExpansive :: ValueEnv -> Int -> Expression a -> Bool
> isNonExpansive _ _ (Literal _ _) = True
> isNonExpansive tyEnv n (Variable _ x)
>   | not (isQualified x) = n == 0 || n < arity x tyEnv
>   | otherwise = n < arity x tyEnv
> isNonExpansive _ _ (Constructor _ _) = True
> isNonExpansive tyEnv n (Apply e1 e2) =
>   isNonExpansive tyEnv (n + 1) e1 && isNonExpansive tyEnv 0 e2
> isNonExpansive tyEnv n (Lambda _ ts e) = n' < 0 || isNonExpansive tyEnv n' e
>   where n' = n - length ts
> isNonExpansive tyEnv n (Let ds e) =
>   all (isNonExpansiveDecl tyEnv) ds && isNonExpansive tyEnv n e
> isNonExpansive _ _ (Case _ _) = False
> isNonExpansive _ _ (Fcase _ _) = False

> isNonExpansiveDecl :: ValueEnv -> Decl a -> Bool
> isNonExpansiveDecl _ (FunctionDecl _ _ _) = True
> isNonExpansiveDecl _ (ForeignDecl _ _ _ _ _ _) = True
> isNonExpansiveDecl tyEnv (PatternDecl _ _ (SimpleRhs _ e _)) =
>   isNonExpansive tyEnv 0 e
> isNonExpansiveDecl _ (FreeDecl _ _) = False

> exprArity :: ValueEnv -> Expression a -> Int
> exprArity _ (Literal _ _) = 0
> exprArity tyEnv (Variable _ x) = arity x tyEnv
> exprArity tyEnv (Constructor _ c) = arity c tyEnv
> exprArity tyEnv (Apply e _) = exprArity tyEnv e - 1
> exprArity tyEnv (Lambda _ ts _) = length ts
> exprArity tyEnv (Let _ e) = exprArity tyEnv e
> exprArity _ (Case _ _) = 0
> exprArity _ (Fcase _ _) = 0

\end{verbatim}
We perform $\eta$-expansion even across newtypes, so that, for
instance, \texttt{doneST} and \texttt{returnST} in the program
fragment 
\begin{verbatim}
  newtype ST s a = ST (s -> (a,s))
  doneST     = returnST ()
  returnST x = ST (\s -> (x,s))
\end{verbatim}
are expanded into functions with arity one and two, respectively. In
order to determine the types of the variables added by
$\eta$-expansion in such cases, the compiler must expand the type
annotations as well. In the example above, the type annotation of
function \texttt{returnST} in the definition of \texttt{doneST} would
be changed from $() \rightarrow \texttt{ST}\,\alpha_1\,()$ to $()
\rightarrow \alpha_1 \rightarrow ((),\alpha_1)$. This is implemented
in function \texttt{expandTypeAnnot}, which tries to expand the type
annotations of $e$'s root such that the expression has (at least)
arity $n$. Note that this may fail when the newtype's definition is
not visible in the current module.
\begin{verbatim}

> expandTypeAnnot :: NewtypeEnv -> Int -> Expression Type
>                 -> (Type,Expression Type)
> expandTypeAnnot nEnv n e
>   | n <= arrowArity ty = (ty,e)
>   | otherwise = (ty',fixType ty' e)
>   where ty = typeOf e
>         ty' = etaType nEnv n ty

> fixType :: Type -> Expression Type -> Expression Type
> fixType ty (Literal _ l) = Literal ty l
> fixType ty (Variable _ v) = Variable ty v
> fixType ty (Constructor _ c) = Constructor ty c
> fixType ty (Apply e1 e2) = Apply (fixType (TypeArrow (typeOf e2) ty) e1) e2
> fixType ty (Lambda p ts e) = Lambda p ts (fixType (foldr match ty ts) e)
>   where match _ (TypeArrow _ ty) = ty
> fixType ty (Let ds e) = Let ds (fixType ty e)
> fixType ty (Case e as) = Case e (map (fixTypeAlt ty) as)
> fixType ty (Fcase e as) = Fcase e (map (fixTypeAlt ty) as)

> fixTypeAlt :: Type -> Alt Type -> Alt Type
> fixTypeAlt ty (Alt p t rhs) = Alt p t (fixTypeRhs ty rhs)

> fixTypeRhs :: Type -> Rhs Type -> Rhs Type
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

> simplifyApp :: ModuleIdent -> Position -> Expression Type -> [Expression Type]
>             -> SimplifyState (Expression Type)
> simplifyApp _ _ (Literal ty l) _ = return (Literal ty l)
> simplifyApp _ _ (Variable ty v) es = return (apply (Variable ty v) es)
> simplifyApp _ _ (Constructor ty c) es = return (apply (Constructor ty c) es)
> simplifyApp m p (Apply e1 e2) es =
>   do
>     e2' <- simplifyApp m p e2 []
>     simplifyApp m p e1 (e2':es)
> simplifyApp _ _ (Lambda p ts e) es = return (apply (Lambda p ts e) es)
> simplifyApp m p (Let ds e) es = liftM (Let ds) (simplifyApp m p e es)
> simplifyApp m p (Case e as) es =
>   do
>     e' <- simplifyApp m p e []
>     mkCase m p (Case e') es as
> simplifyApp m p (Fcase e as) es =
>   do
>     e' <- simplifyApp m p e []
>     mkCase m p (Fcase e') es as

> mkCase :: ModuleIdent -> Position -> ([Alt Type] -> Expression Type)
>        -> [Expression Type] -> [Alt Type] -> SimplifyState (Expression Type)
> mkCase m p f es as
>   | length as == 1 = return (f (map (applyToAlt es) as))
>   | otherwise =
>       do
>         vs <- mapM (freshVar m argId) es
>         let es' = map (uncurry mkVar) vs
>         return (foldr2 mkLet (f (map (applyToAlt es') as)) vs es)
>   where argId n = mkIdent ("_#arg" ++ show n)
>         applyToAlt es (Alt p t rhs) = Alt p t (applyToRhs es rhs)
>         applyToRhs es (SimpleRhs p e _) = SimpleRhs p (apply e es) []
>         mkLet (ty,v) e1 e2 = Let [varDecl p ty v e1] e2

\end{verbatim}
Variables that are bound to (simple) constants and aliases to other
variables are substituted. In terms of conventional compiler
technology, these optimizations correspond to constant folding and
copy propagation, respectively. The transformation is applied
recursively to a substituted variable in order to handle chains of
variable definitions. Note that the compiler carefully updates the
type annotations of the inlined expression. This is necessary in order
to preserve soundness of the annotations when inlining a variable with
a polymorphic type because in that case each use of the variable is
annotated with fresh type variables that are unrelated to the type
variables used on the right hand side of the variable's definition. In
addition, newtype constructors in the result of the substituted
expression's type are expanded as far as necessary to ensure that the
annotated type has the same arity before and after the substitution.

\ToDo{Apply the type substitution only when necessary, i.e., when the
  inlined variable has a polymorphic type.}

The bindings of a let expression are sorted topologically in
order to split them into minimal binding groups. In addition,
local declarations occurring on the right hand side of a pattern
declaration are lifted into the enclosing binding group using the
equivalence (modulo $\alpha$-conversion) of \texttt{let}
$x$~=~\texttt{let} \emph{decls} \texttt{in} $e_1$ \texttt{in} $e_2$
and \texttt{let} \emph{decls}\texttt{;} $x$~=~$e_1$ \texttt{in} $e_2$.
This transformation avoids the creation of some redundant lifted
functions in later phases of the compiler.
\begin{verbatim}

> simplifyExpr :: ModuleIdent -> InlineEnv -> Expression Type
>              -> SimplifyState (Expression Type)
> simplifyExpr _ _ (Literal ty l) = return (Literal ty l)
> simplifyExpr m env (Variable ty v)
>   | isQualified v = return (Variable ty v)
>   | otherwise =
>       do
>         nEnv <- liftSt envRt
>         maybe (return (Variable ty v))
>               (simplifyExpr m env . substExpr nEnv ty)
>               (lookupEnv (unqualify v) env)
>   where substExpr nEnv ty =
>           snd . expandTypeAnnot nEnv (arrowArity ty) . withType nEnv ty
> simplifyExpr _ _ (Constructor ty c) = return (Constructor ty c)
> simplifyExpr m env (Apply e1 e2) =
>   do
>     e1' <- simplifyExpr m env e1
>     e2' <- simplifyExpr m env e2
>     return (Apply e1' e2')
> simplifyExpr m env (Lambda p ts e) =
>   do
>     e' <- simplifyApp m p e [] >>= simplifyExpr m env
>     tyEnv <- fetchSt
>     nEnv <- liftSt envRt
>     (ts',e'') <- etaExpr m tyEnv nEnv e'
>     return (etaReduce m tyEnv p (ts ++ ts') e'')
> simplifyExpr m env (Let ds e) =
>   do
>     dss' <- mapM (sharePatternRhs m) (foldr hoistDecls [] ds)
>     simplifyLet m env (scc bv (qfv m) (concat dss')) e
> simplifyExpr m env (Case e as) =
>   do
>     e' <- simplifyExpr m env e
>     maybe (liftM (Case e') (mapM (simplifyAlt m env) as))
>           (simplifyExpr m env)
>           (simplifyMatch e' as)
> simplifyExpr m env (Fcase e as) =
>   do
>     e' <- simplifyExpr m env e
>     maybe (liftM (Fcase e') (mapM (simplifyAlt m env) as))
>           (simplifyExpr m env)
>           (simplifyMatch e' as)

> simplifyAlt :: ModuleIdent -> InlineEnv -> Alt Type
>             -> SimplifyState (Alt Type)
> simplifyAlt m env (Alt p t rhs) = liftM (Alt p t) (simplifyRhs m env rhs)

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
constructor, or a non-nullary function. Note that it is not possible
to define nullary functions in local declarations in Curry. Thus, an
unqualified name always refers to either a variable or a non-nullary
function. Applications of constructors and partial applications of
functions to at least one argument are not inlined in order to avoid
code duplication (for the allocation of the terms). In order to
prevent non-termination, no inlining is performed for entities defined
in recursive binding groups.

With the list of inlineable expressions, the body of the let is
simplified and then the declaration groups are processed from inside
to outside to construct the simplified, nested let expression. In
doing so unused bindings are discarded. In addition, all pattern
bindings are replaced by simple variable declarations using selector
functions to access the pattern variables.
\begin{verbatim}

> simplifyLet :: ModuleIdent -> InlineEnv -> [[Decl Type]] -> Expression Type
>             -> SimplifyState (Expression Type)
> simplifyLet m env [] e = simplifyExpr m env e
> simplifyLet m env (ds:dss) e =
>   do
>     ds' <- mapM (simplifyDecl m env) ds
>     tyEnv <- fetchSt
>     nEnv <- liftSt envRt
>     trEnv <- liftSt (liftRt envRt)
>     e' <- simplifyLet m (inlineVars m tyEnv trEnv ds' env) dss e
>     dss'' <- mapM (expandPatternBindings m (qfv m ds' ++ qfv m e')) ds'
>     return (mkSimplLet m nEnv (concat dss'') e')

> inlineVars :: ModuleIdent -> ValueEnv -> TrustEnv -> [Decl Type] -> InlineEnv
>            -> InlineEnv
> inlineVars m tyEnv trEnv
>            [FunctionDecl _ f [Equation p (FunLhs _ ts) (SimpleRhs _ e _)]]
>            env
>   | f `notElem` qfv m e && maybe True (Trust==) (lookupEnv f trEnv) =
>       case etaReduce m tyEnv p ts e of
>         Lambda _ _ _ -> env
>         e' -> bindEnv f e' env
> inlineVars m tyEnv _
>            [PatternDecl _ (VariablePattern _ v) (SimpleRhs _ e _)]
>            env
>   | canInline tyEnv e && v `notElem` qfv m e = bindEnv v e env
> inlineVars _ _ _ _ env = env

> etaReduce :: ModuleIdent -> ValueEnv -> Position -> [ConstrTerm Type]
>           -> Expression Type -> Expression Type
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

> mkSimplLet :: ModuleIdent -> NewtypeEnv -> [Decl Type] -> Expression Type
>            -> Expression Type
> mkSimplLet m _ [FreeDecl p vs] e
>   | null vs' = e
>   | otherwise = Let [FreeDecl p vs'] e
>   where vs' = filter (`elem` qfv m e) vs
> mkSimplLet m nEnv [PatternDecl _ (VariablePattern _ v) (SimpleRhs _ e _)]
>       (Variable ty' v')
>   | v' == qualify v && v `notElem` qfv m e = withType nEnv ty' e
> mkSimplLet m _ ds e
>   | null (filter (`elem` qfv m e) (bv ds)) = e
>   | otherwise = Let ds e

\end{verbatim}
When the scrutinized expression in a $($f$)$case expression is a
literal or a constructor application, the compiler can perform the
pattern matching already at compile time and simplify the case
expression to the right hand side of the matching alternative or to
\texttt{Prelude.failed} if no alternative matches. When a case
expression collapses to a matching alternative, the pattern variables
are bound to the matching (sub)terms of the scrutinized expression. We
have to be careful with as-patterns in order to avoid losing sharing
by code duplication. For instance, the expression
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
form where all arguments of applications are variables.
\begin{verbatim}

> simplifyMatch :: Expression Type -> [Alt Type] -> Maybe (Expression Type)
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
> unapply (Apply e1 e2) es = unapply e1 (e2:es)
> unapply (Lambda p ts e) es = (Lambda p ts e,es)
> unapply (Let ds e) es = (Let ds e,es)
> unapply (Case e as) es = (Case e as,es)
> unapply (Fcase e as) es = (Fcase e as,es)

> match :: Either (Type,Literal) (Type,QualIdent,[Expression Type])
>       -> [Alt Type] -> Expression Type
> match e as =
>   head ([expr p t rhs | Alt p t rhs <- as, t `matches` e] ++
>         [prelFailed (typeOf (Case (matchExpr e) as))])
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
>             -> Either (Type,Literal) (Type,QualIdent,[Expression Type])
>             -> ConstrTerm Type -> Expression Type -> Expression Type
> bindPattern _ (Left _) (LiteralPattern _ _) e' = e'
> bindPattern p (Right (_,_,es)) (ConstructorPattern _ _ ts) e' =
>   foldr Let e' [zipWith (\(VariablePattern ty v) e -> varDecl p ty v e) ts es]
> bindPattern p e (VariablePattern ty v) e' =
>   Let [varDecl p ty v (matchExpr e)] e'
> bindPattern p e (AsPattern v t) e' = bindPattern p e t (Let [bindAs p v t] e')

> bindAs :: Position -> Ident -> ConstrTerm Type -> Decl Type
> bindAs p v (LiteralPattern ty l) = varDecl p ty v (Literal ty l)
> bindAs p v (VariablePattern ty v') = varDecl p ty v (mkVar ty v')
> bindAs p v (ConstructorPattern ty c ts) = varDecl p ty v e'
>   where e' = apply (Constructor (foldr (TypeArrow . typeOf) ty ts) c)
>                    [mkVar ty v | VariablePattern ty v <- ts]
> bindAs p v (AsPattern v' t') = varDecl p ty v (mkVar ty v')
>   where ty = typeOf t'

> prelFailed :: a -> Expression a
> prelFailed ty = Variable ty (qualifyWith preludeMIdent (mkIdent "failed"))

\end{verbatim}
\label{pattern-binding}
In order to implement lazy pattern matching in local declarations,
pattern declarations $t$~\texttt{=}~$e$ where $t$ is not a variable
are transformed into a list of declarations
$v_0$~\texttt{=}~$e$\texttt{;} $v_1$~\texttt{=}~$f_1$~$v_0$\texttt{;}
\dots{} \texttt{;} $v_n$~\texttt{=}~$f_n$~$v_0$ where $v_0$ is a fresh
variable, $v_1,\dots,v_n$ are the variables occurring in $t$ and the
auxiliary functions $f_i$ are defined by $f_i$~$t$~\texttt{=}~$v_i$
(see also appendix D.8 of the Curry report~\cite{Hanus:Report}). The
binding $v_0$~\texttt{=}~$e$ is introduced before splitting the
declaration groups of the enclosing let expression (cf.\ the
\texttt{Let} case in \texttt{simplifyExpr} above) so that they are
placed in their own declaration group whenever possible. In
particular, this ensures that the new binding is discarded when the
expression $e$ is a variable itself.

Unfortunately, this transformation introduces a well-known space
leak~\cite{Wadler87:Leaks,Sparud93:Leaks} because the matched
expression cannot be garbage collected until all of the matched
variables have been evaluated. Consider the following function:
\begin{verbatim}
  f x | all (' ' ==) cs = c where (c:cs) = x
\end{verbatim}
One might expect the call \verb|f (replicate 10000 ' ')| to execute in
constant space because (the tail of) the long list of blanks is
consumed and discarded immediately by \texttt{all}. However, the
application of the selector function that extracts the head of the
list is not evaluated until after the guard has succeeded and thus
prevents the list from being garbage collected.

In order to avoid this space leak we use the approach
from~\cite{Sparud93:Leaks} and update all pattern variables when one
of the selector functions has been evaluated. Therefore all pattern
variables except for the matched one are passed as additional
arguments to each of the selector functions. Thus, each of these
variables occurs twice in the argument list of a selector function,
once in the first argument and also as one of the remaining arguments.
This duplication of names is used by the compiler to insert the code
that updates the variables when generating abstract machine code.

We will add only those pattern variables as additional arguments which
are actually used in the code. This reduces the number of auxiliary
variables and can prevent the introduction of a recursive binding
group when only a single variable is used. It is also the reason for
performing this transformation here instead of in the \texttt{Desugar}
module. The selector functions are defined in a local declaration on
the right hand side of a projection declaration so that there is
exactly one declaration for each used variable.

Note that case matching has transformed pattern declarations of the
form $t$~\texttt{=}~$e$ into a (pseudo-)\discretionary{}{}{} flattened
form $t$~\texttt{=} \texttt{fcase}~$e$~\texttt{of}
\texttt{\char`\{}~$\dots{}\rightarrow t$~\texttt{\char`\}}, where the
\texttt{fcase} expression on the right hand side contains only flat
patterns.
\begin{verbatim}

> sharePatternRhs :: ModuleIdent -> Decl Type -> SimplifyState [Decl Type]
> sharePatternRhs m (PatternDecl p t rhs) =
>   case (t,rhs) of
>     (VariablePattern _ _,_) -> return [PatternDecl p t rhs]
>     (_,SimpleRhs p' (Fcase e as) _) ->
>       do
>         (ty,v) <- freshVar m patternId t
>         return [PatternDecl p t (SimpleRhs p' (Fcase (mkVar ty v) as) []),
>                 PatternDecl p (VariablePattern ty v) (SimpleRhs p e [])]
>   where patternId n = mkIdent ("_#pat" ++ show n)
> sharePatternRhs _ d = return [d]

> expandPatternBindings :: ModuleIdent -> [Ident] -> Decl Type
>                       -> SimplifyState [Decl Type]
> expandPatternBindings m fvs (PatternDecl p t rhs) =
>   case (t,rhs) of
>     (VariablePattern _ _,_) -> return [PatternDecl p t rhs]
>     (_,SimpleRhs _ e@(Fcase (Variable ty v) _) _) ->
>       mapM (projectionDecl m p v0 e) (shuffle vs)
>       where vs = filter ((`elem` fvs) . snd) (vars t)
>             v0 = (ty,unqualify v)
> expandPatternBindings _ _ d = return [d]

> projectionDecl :: ModuleIdent -> Position -> (Type,Ident) -> Expression Type
>                -> [(Type,Ident)] -> SimplifyState (Decl Type)
> projectionDecl m p v0 (Fcase _ as) (v:vs) =
>   do
>     f <- freshIdent m selectorId (length vs') (polyType ty)
>     return (uncurry (varDecl p) v $
>             Let [funDecl p f ts (project e' (uncurry mkVar v))]
>                 (apply (mkVar ty f) es))
>   where vs' = v0:vs
>         ty = foldr TypeArrow (fst v) (map fst vs')
>         v0' = head ([(fst v0,v) | Alt _ (AsPattern v _) _ <- as] ++ [v0])
>         ts = map (uncurry VariablePattern) (v0':vs)
>         e' = Fcase (uncurry mkVar v0') as
>         es = map (uncurry mkVar) vs'
>         project (Variable _ _) e = e
>         project (Apply _ _) e = e
>         project (Fcase e [Alt p t (SimpleRhs p' e' _)]) e'' =
>           Fcase e [Alt p t (SimpleRhs p' (project e' e'') [])]

\end{verbatim}
Auxiliary functions
\begin{verbatim}

> trustedFun :: TrustEnv -> Ident -> Bool
> trustedFun trEnv f = maybe True (Trust ==) (lookupEnv f trEnv)

> freshIdent :: ModuleIdent -> (Int -> Ident) -> Int -> TypeScheme
>            -> SimplifyState Ident
> freshIdent m f n ty =
>   do
>     x <- liftM f (liftSt (liftRt (liftRt (updateSt (1 +)))))
>     updateSt_ (bindFun m x n ty)
>     return x

> freshVar :: Typeable a => ModuleIdent -> (Int -> Ident) -> a
>          -> SimplifyState (Type,Ident)
> freshVar m f x =
>   do
>     v <- freshIdent m f 0 (monoType ty)
>     return (ty,v)
>   where ty = typeOf x

> vars :: ConstrTerm Type -> [(Type,Ident)]
> vars (LiteralPattern _ _) = []
> vars (VariablePattern ty v) = [(ty,v)]
> vars (ConstructorPattern _ _ ts) = concatMap vars ts
> vars (AsPattern v t) = (typeOf t,v) : vars t

> shuffle :: [a] -> [[a]]
> shuffle xs = shuffle id xs
>   where shuffle _ [] = []
>         shuffle f (x:xs) = (x : f xs) : shuffle (f . (x:)) xs

\end{verbatim}
