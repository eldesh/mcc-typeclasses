% -*- LaTeX -*-
% $Id: Simplify.lhs 2161 2007-04-22 14:48:33Z wlux $
%
% Copyright (c) 2003-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Simplify.lhs}
\section{Optimizing the Desugared Code}\label{sec:simplify}
After desugaring the source code, but before lifting local
declarations, the compiler performs a few simple optimizations to
improve the efficiency of the generated code. In addition, the
optimizer replaces pattern bindings with simple variable bindings and
selector functions.

Currently, the following optimizations are implemented:
\begin{itemize}
\item Remove unused declarations.
\item Inline simple constants.
\item Compute minimal binding groups.
\item Under certain conditions, inline local function definitions.
\end{itemize}
\begin{verbatim}

> module Simplify(simplify) where
> import Base
> import Combined
> import Env
> import Monad
> import SCC
> import Typing
> import Utils

> type SimplifyState a = StateT ValueEnv (ReaderT TrustEnv (StateT Int Id)) a
> type InlineEnv = Env Ident (Expression Type)

> simplify :: ValueEnv -> TrustEnv -> Module Type -> (Module Type,ValueEnv)
> simplify tyEnv trEnv m =
>   runSt (callRt (callSt (simplifyModule m) tyEnv) trEnv) 1

> simplifyModule :: Module Type -> SimplifyState (Module Type,ValueEnv)
> simplifyModule (Module m es is ds) =
>   do
>     ds' <- mapM (simplifyTopDecl m) ds
>     tyEnv <- fetchSt
>     return (Module m es is ds',tyEnv)

> simplifyTopDecl :: ModuleIdent -> TopDecl Type -> SimplifyState (TopDecl Type)
> simplifyTopDecl m (BlockDecl d) = liftM BlockDecl (simplifyDecl m emptyEnv d)
> simplifyTopDecl _ d = return d

> simplifyDecl :: ModuleIdent -> InlineEnv -> Decl Type
>              -> SimplifyState (Decl Type)
> simplifyDecl m env (FunctionDecl p f eqs) =
>   liftM (FunctionDecl p f . concat) (mapM (simplifyEquation m env) eqs)
> simplifyDecl m env (PatternDecl p t rhs) =
>   liftM (PatternDecl p t) (simplifyRhs m env rhs)
> simplifyDecl _ _ d = return d

\end{verbatim}
After simplifying the right hand side of an equation, the compiler
transforms declarations of the form
\begin{quote}\tt
  $f\;t_1\dots t_{k}\;x_{k+1}\dots x_{n}$ =
    let $g\;t_{k+1}\dots t_{n}$ = $e$ in
    $g\;x_{k+1}\dots x_{n}$
\end{quote}
into the equivalent definition
\begin{quote}\tt
  $f\;t_1\dots t_{k}\;(x_{k+1}$@$t_{k+1})\dots(x_n$@$t_{n})$ = $e$
\end{quote}
where the arities of $f$ and $g$ are $n$ and $n-k$, respectively,
and $x_{k+1},\dots,x_{n}$ are variables. This optimization was
introduced in order to avoid an auxiliary function being generated for
definitions whose right-hand side is a $\lambda$-expression, e.g.,
\verb|f . g = \x -> f (g x)|. This declaration is transformed into
\verb|(.) f g x = let lambda x = f (g x) in lambda x| by desugaring
and in turn is optimized into \verb|(.) f g x = f (g x)|, here. The
transformation can obviously be generalized to the case where $g$ is
defined by more than one equation.

We have to be careful with this optimization in conjunction with
newtype constructors. It is possible that the local function is
applied only partially, e.g., for
\begin{verbatim}
  newtype ST s a = ST (s -> (a,s))
  returnST x = ST (\s -> (x,s))
\end{verbatim}
the desugared code is equivalent to
\begin{verbatim}
  returnST x = let lambda1 s = (x,s) in lambda1
\end{verbatim}
We must not ``optimize'' this into \texttt{returnST x s = (x,s)}
because the compiler assumes that \texttt{returnST} is a unary
function.

Note that this transformation is not strictly semantic preserving as
the evaluation order of arguments can be changed. This happens if $f$
is defined by more than one rule with overlapping patterns and the
local functions of each rule have disjoint patterns. As an example,
consider the function
\begin{verbatim}
  f (Just x) _ = let g (Left z)  = x + z in g
  f _ (Just y) = let h (Right z) = y + z in h
\end{verbatim}
The definition of \texttt{f} is non-deterministic because of the
overlapping patterns in the first and second argument. However, the
optimized definition
\begin{verbatim}
  f (Just x) _ (Left z)  = x + z
  f _ (Just y) (Right z) = y + z
\end{verbatim}
is deterministic. It will evaluate and match the third argument first,
whereas the original definition is going to evaluate the first or the
second argument first, depending on the non-deterministic branch
chosen. As such definitions are presumably rare, and the optimization
avoids a non-deterministic split of the computation, we put up with
the change of evaluation order.

This transformation is actually just a special case of inlining a
(local) function definition. We are unable to handle the general case
because it would require representing pattern matching code explicitly
in Curry expressions.
\begin{verbatim}

> simplifyEquation :: ModuleIdent -> InlineEnv -> Equation Type
>                  -> SimplifyState [Equation Type]
> simplifyEquation m env (Equation p lhs rhs) =
>   do
>     rhs' <- simplifyRhs m env rhs
>     tyEnv <- fetchSt
>     trEnv <- liftSt envRt
>     return (inlineFun m tyEnv trEnv p lhs rhs')

> inlineFun :: ModuleIdent -> ValueEnv -> TrustEnv -> Position -> Lhs Type
>           -> Rhs Type -> [Equation Type]
> inlineFun m tyEnv trEnv p (FunLhs f ts)
>           (SimpleRhs _ (Let [FunctionDecl _ g eqs'] e) _)
>   | g `notElem` qfv m eqs' && e' == Variable (typeOf e') (qualify g) &&
>     n == arity (qualify g) tyEnv && trustedFun trEnv g =
>     map (merge p f ts' vs') eqs'
>   where n :: Int                      -- type signature necessary for nhc
>         (n,vs',ts',e') = etaReduce 0 [] (reverse ts) e
>         merge p f ts vs (Equation _ (FunLhs _ ts') rhs) =
>           Equation p (FunLhs f (ts ++ zipWith AsPattern vs ts')) rhs
>         etaReduce n vs (VariablePattern _ v : ts) (Apply e (Variable _ v'))
>           | qualify v == v' = etaReduce (n+1) (v:vs) ts e
>         etaReduce n vs ts e = (n,vs,reverse ts,e)
> inlineFun _ _ _ p lhs rhs = [Equation p lhs rhs]

> simplifyRhs :: ModuleIdent -> InlineEnv -> Rhs Type
>             -> SimplifyState (Rhs Type)
> simplifyRhs m env (SimpleRhs p e _) =
>   do
>     e' <- simplifyApp m p e [] >>= simplifyExpr m env
>     return (SimpleRhs p e' [])

\end{verbatim}
Before other optimizations are applied to expressions, the simplifier
first transforms applications of let and case expressions by pushing
the application down into the body of let expressions and into the
alternatives of case expressions, respectively. In order to avoid code
duplication, arguments that are pushed into the alternatives of a case
expression by this transformation are bound to local variables (unless
there is only one alternative). If these arguments are just simple
variables or constant literals, the optimizations performed in
\texttt{simplifyExpr} below will substitute these values and the let
declarations will be removed.
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
> simplifyApp m p (Let ds e) es = liftM (Let ds) (simplifyApp m p e es)
> simplifyApp m p (Case e as) es =
>   do
>     e' <- simplifyApp m p e []
>     mkCase e' es as
>   where argId n = mkIdent ("_#arg" ++ show n)
>         mkCase e es as
>           | length as == 1 = return (Case e (map (applyToAlt es) as))
>           | otherwise =
>               do
>                 vs <- mapM (freshVar m argId) es
>                 let es' = map (uncurry mkVar) vs
>                 return (foldr2 mkLet (Case e (map (applyToAlt es') as)) vs es)
>         applyToAlt es (Alt p t rhs) = Alt p t (applyToRhs es rhs)
>         applyToRhs es (SimpleRhs p e _) = SimpleRhs p (apply e es) []
>         mkLet (ty,v) e1 e2 = Let [varDecl p ty v e1] e2

\end{verbatim}
Variables that are bound to (simple) constants and aliases to other
variables are substituted. In terms of conventional compiler
technology these optimizations correspond to constant folding and copy
propagation, respectively. The transformation is applied recursively
to a substituted variable in order to handle chains of variable
definitions.

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
>   | otherwise = maybe (return (Variable ty v)) (simplifyExpr m env)
>                       (lookupEnv (unqualify v) env)
> simplifyExpr _ _ (Constructor ty c) = return (Constructor ty c)
> simplifyExpr m env (Apply e1 e2) =
>   do
>     e1' <- simplifyExpr m env e1
>     e2' <- simplifyExpr m env e2
>     return (Apply e1' e2')
> simplifyExpr m env (Let ds e) =
>   do
>     dss' <- mapM (sharePatternRhs m) ds
>     simplifyLet m env (scc bv (qfv m) (foldr hoistDecls [] (concat dss'))) e
> simplifyExpr m env (Case e alts) =
>   do
>     e' <- simplifyExpr m env e
>     maybe (liftM (Case e') (mapM (simplifyAlt m env) alts))
>           (simplifyExpr m env)
>           (simplifyMatch e' alts)

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
and aliases to other variables are inlined. A constant is considered
simple if it is either a literal, a constructor, or a non-nullary
function. Note that it is not possible to define nullary functions in
local declarations in Curry. Thus, an unqualified name always refers
to either a variable or a non-nullary function.  Applications of
constructors and partial applications of functions to at least one
argument are not inlined because the compiler has to allocate space
for them, anyway. In order to prevent non-termination, recursive
binding groups are not processed.

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
>     e' <- simplifyLet m (inlineVars tyEnv ds' env) dss e
>     dss'' <- mapM (expandPatternBindings m tyEnv (qfv m ds' ++ qfv m e')) ds'
>     return (mkLet m (concat dss'') e')

> inlineVars :: ValueEnv -> [Decl Type] -> InlineEnv -> InlineEnv
> inlineVars tyEnv [PatternDecl _ (VariablePattern _ v) (SimpleRhs _ e _)] env
>   | canInline e = bindEnv v e env
>   where canInline (Literal _ _) = True
>         canInline (Constructor _ _) = True
>         canInline (Variable _ v')
>           | isQualified v' = arity v' tyEnv > 0
>           | otherwise = v /= unqualify v'
>         canInline _ = False
> inlineVars _ _ env = env

> mkLet :: ModuleIdent -> [Decl Type] -> Expression Type -> Expression Type
> mkLet m [FreeDecl p vs] e
>   | null vs' = e
>   | otherwise = Let [FreeDecl p vs'] e
>   where vs' = filter (`elem` qfv m e) vs
> mkLet m [PatternDecl _ (VariablePattern _ v) (SimpleRhs _ e _)]
>       (Variable _ v')
>   | v' == qualify v && v `notElem` qfv m e = e
> mkLet m ds e
>   | null (filter (`elem` qfv m e) (bv ds)) = e
>   | otherwise = Let ds e

\end{verbatim}
When the scrutinized expression in a case expression is a literal or a
constructor application, the compiler can perform the pattern matching
already at compile time and simplify the case expression to the right
hand side of the matching alternative or to \texttt{Prelude.failed} if
no alternative matches. When a case expression collapses to a matching
alternative, the pattern variables are bound to the matching
(sub)terms of the scrutinized expression. We have to be careful with
as-patterns in order to avoid losing sharing by code duplication. For
instance, the expression
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
> simplifyMatch e =
>   case unapply e [] of
>     (dss,Literal ty l,_) -> Just . match dss (Left (ty,l))
>     (dss,Constructor ty c,es) -> Just . match dss (Right (ty,c,es))
>     (_,_,_) -> const Nothing

> unapply :: Expression a -> [Expression a]
>         -> ([[Decl a]],Expression a,[Expression a])
> unapply (Literal ty l) es = ([],Literal ty l,es)
> unapply (Variable ty v) es = ([],Variable ty v,es)
> unapply (Constructor ty c) es = ([],Constructor ty c,es)
> unapply (Apply e1 e2) es = unapply e1 (e2:es)
> unapply (Let ds e) es = (ds:dss',e',es')
>   where (dss',e',es') = unapply e es
> unapply (Case e alts) es = ([],Case e alts,es)

> match :: [[Decl Type]]
>       -> Either (Type,Literal) (Type,QualIdent,[Expression Type])
>       -> [Alt Type] -> Expression Type
> match dss e alts =
>   head ([expr p t rhs | Alt p t rhs <- alts, t `matches` e] ++
>         [prelFailed (typeOf (Case (matchExpr e) alts))])
>   where expr p t (SimpleRhs _ e' _) = foldr Let e' (dss ++ bindPattern p e t)

> matches :: ConstrTerm Type
>         -> Either (Type,Literal) (Type,QualIdent,[Expression Type])
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
>             -> ConstrTerm Type -> [[Decl Type]]
> bindPattern _ (Left _) (LiteralPattern _ _) = []
> bindPattern p (Right (_,_,es)) (ConstructorPattern _ _ ts) =
>   [zipWith (\(VariablePattern ty v) -> varDecl p ty v) ts es]
> bindPattern p e (VariablePattern ty v) = [[varDecl p ty v (matchExpr e)]]
> bindPattern p e (AsPattern v t) = bindPattern p e t ++ [[bindAs p v t]]

> bindAs :: Position -> Ident -> ConstrTerm Type -> Decl Type
> bindAs p v (LiteralPattern ty l) = varDecl p ty v (Literal ty l)
> bindAs p v (VariablePattern ty v') = varDecl p ty v (mkVar ty v')
> bindAs p v (ConstructorPattern ty c ts) = varDecl p ty v e'
>   where e' = apply (Constructor (foldr (TypeArrow . typeOf) ty ts) c)
>                    [mkVar ty v | VariablePattern ty v <- ts]
> bindAs p v (AsPattern v' t') = varDecl p ty v (mkVar ty v')
>   where ty = typeOf t'

> prelFailed :: Type -> Expression Type
> prelFailed ty = Variable ty (qualifyWith preludeMIdent (mkIdent "failed"))

\end{verbatim}
\label{pattern-binding}
In order to implement lazy pattern matching in local declarations,
pattern declarations $t$~\texttt{=}~$e$ where $t$ is not a variable
are transformed into a list of declarations
$v_0$~\texttt{=}~$e$\texttt{;} $v_1$~\texttt{=}~$f_1$~$v_0$\texttt{;}
\dots{} $v_n$~\texttt{=}~$f_n$~$v_0$ where $v_0$ is a fresh variable,
$v_1,\dots,v_n$ are the variables occurring in $t$ and the auxiliary
functions $f_i$ are defined by $f_i$~$t$~\texttt{=}~$v_i$ (see also
appendix D.8 of the Curry report~\cite{Hanus:Report}). The bindings
$v_0$~\texttt{=}~$e$ are introduced before splitting the declaration
groups of the enclosing let expression (cf. the \texttt{Let} case in
\texttt{simplifyExpr} above) so that they are placed in their own
declaration group whenever possible. In particular, this ensures that
the new binding is discarded when the expression $e$ is itself a
variable.

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
\begin{verbatim}

> sharePatternRhs :: ModuleIdent -> Decl Type -> SimplifyState [Decl Type]
> sharePatternRhs m (PatternDecl p t rhs) =
>   case t of
>     VariablePattern _ _ -> return [PatternDecl p t rhs]
>     _ -> 
>       do
>         (ty,v) <- freshVar m patternId t
>         return [PatternDecl p t (SimpleRhs p (mkVar ty v) []),
>                 PatternDecl p (VariablePattern ty v) rhs]
>   where patternId n = mkIdent ("_#pat" ++ show n)
> sharePatternRhs _ d = return [d]

> expandPatternBindings :: ModuleIdent -> ValueEnv -> [Ident] -> Decl Type
>                       -> SimplifyState [Decl Type]
> expandPatternBindings m tyEnv fvs (PatternDecl p t (SimpleRhs p' e _)) =
>   case t of
>     VariablePattern _ _ -> return [PatternDecl p t (SimpleRhs p' e [])]
>     _ ->
>       do
>         fs <- mapM (freshIdent m selectorId n . polyType) selectorTys
>         return (zipWith3 (projectionDecl p t e) selectorTys fs
>                          (shuffle (zip tys vs)))
>       where n = length vs
>             vs = filter (`elem` fvs) (bv t)
>             ty = typeOf t
>             tys = map (rawType . flip varType tyEnv) vs
>             selectorTys = map (selectorType ty) (shuffle tys)
>             selectorType ty0 (ty:tys) = foldr TypeArrow ty (ty0:tys)
>             selectorDecl p f t (v:vs) =
>               funDecl p f (t:map (uncurry VariablePattern) vs)
>                       (uncurry mkVar v)
>             projectionDecl p t e ty f (v:vs) =
>               uncurry (varDecl p) v
>                       (Let [selectorDecl p f t (v:vs)]
>                            (apply (mkVar ty f) (e : map (uncurry mkVar) vs)))
> expandPatternBindings _ _ _ d = return [d]

\end{verbatim}
Auxiliary functions
\begin{verbatim}

> trustedFun :: TrustEnv -> Ident -> Bool
> trustedFun trEnv f = maybe True (Trust ==) (lookupEnv f trEnv)

> freshIdent :: ModuleIdent -> (Int -> Ident) -> Int -> TypeScheme
>            -> SimplifyState Ident
> freshIdent m f n ty =
>   do
>     x <- liftM f (liftSt (liftRt (updateSt (1 +))))
>     updateSt_ (bindFun m x n ty)
>     return x

> freshVar :: Typeable a => ModuleIdent -> (Int -> Ident) -> a
>          -> SimplifyState (Type,Ident)
> freshVar m f x = liftM ((,) ty) (freshIdent m f 0 (monoType ty))
>   where ty = typeOf x

> shuffle :: [a] -> [[a]]
> shuffle xs = shuffle id xs
>   where shuffle _ [] = []
>         shuffle f (x:xs) = (x : f xs) : shuffle (f . (x:)) xs

> apply :: Expression a -> [Expression a] -> Expression a
> apply = foldl Apply

> mkVar :: a -> Ident -> Expression a
> mkVar ty = Variable ty . qualify

> varDecl :: Position -> a -> Ident -> Expression a -> Decl a
> varDecl p ty v e = PatternDecl p (VariablePattern ty v) (SimpleRhs p e [])

> funDecl :: Position -> Ident -> [ConstrTerm a] -> Expression a -> Decl a
> funDecl p f ts e =
>   FunctionDecl p f [Equation p (FunLhs f ts) (SimpleRhs p e [])]

\end{verbatim}
