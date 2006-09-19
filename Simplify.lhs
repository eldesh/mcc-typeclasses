% -*- LaTeX -*-
% $Id: Simplify.lhs 1875 2006-03-18 18:43:27Z wlux $
%
% Copyright (c) 2003-2006, Wolfgang Lux
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

> type SimplifyState a = StateT ValueEnv (StateT Int Id) a
> type InlineEnv = Env Ident Expression

> simplify :: ValueEnv -> Module -> (Module,ValueEnv)
> simplify tyEnv m = runSt (callSt (simplifyModule m) tyEnv) 1

> simplifyModule :: Module -> SimplifyState (Module,ValueEnv)
> simplifyModule (Module m es is ds) =
>   do
>     ds' <- mapM (simplifyTopDecl m) ds
>     tyEnv <- fetchSt
>     return (Module m es is ds',tyEnv)

> simplifyTopDecl :: ModuleIdent -> TopDecl -> SimplifyState TopDecl
> simplifyTopDecl m (BlockDecl d) = liftM BlockDecl (simplifyDecl m emptyEnv d)
> simplifyTopDecl _ d = return d

> simplifyDecl :: ModuleIdent -> InlineEnv -> Decl -> SimplifyState Decl
> simplifyDecl m env (FunctionDecl p f eqs) =
>   liftM (FunctionDecl p f . concat) (mapM (simplifyEquation m env) eqs)
> simplifyDecl m env (PatternDecl p t rhs) =
>   liftM (PatternDecl p t) (simplifyRhs m env rhs)
> simplifyDecl _ _ d = return d

\end{verbatim}
After simplifying the right hand side of an equation, the compiler
transforms declarations of the form
\begin{quote}\tt
  $f\;t_1\dots t_{k-k'}\;x_{k-k'+1}\dots x_{k}$ =
    let $f'\;t'_1\dots t'_{k'}$ = $e$ in
    $f'\;x_1\dots x_{k'}$
\end{quote}
into the equivalent definition
\begin{quote}\tt
  $f\;t_1\dots t_{k-k'}\;(x_{k-k'+1}$@$t'_1)\dots(x_k$@$t'_{k'})$ = $e$
\end{quote}
where the arities of $f$ and $f'$ are $k$ and $k'$, respectively, and
$x_{k-k'+1},\dots,x_{k}$ are variables. This optimization was
introduced in order to avoid an auxiliary function being generated for
definitions whose right-hand side is a $\lambda$-expression, e.g.,
\verb|f . g = \x -> f (g x)|. This declaration is transformed into
\verb|(.) f g x = let lambda x = f (g x) in lambda x| by desugaring
and in turn is optimized into \verb|(.) f g x = f (g x)|, here. The
transformation can obviously be generalized to the case where $f'$ is
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
because it would require to represent the pattern matching code
explicitly in a Curry expression.
\begin{verbatim}

> simplifyEquation :: ModuleIdent -> InlineEnv -> Equation
>                  -> SimplifyState [Equation]
> simplifyEquation m env (Equation p lhs rhs) =
>   do
>     rhs' <- simplifyRhs m env rhs
>     tyEnv <- fetchSt
>     return (inlineFun m tyEnv p lhs rhs')

> inlineFun :: ModuleIdent -> ValueEnv -> Position -> Lhs -> Rhs -> [Equation]
> inlineFun m tyEnv p (FunLhs f ts)
>           (SimpleRhs _ (Let [FunctionDecl _ f' eqs'] e) _)
>   | f' `notElem` qfv m eqs' && e' == Variable (qualify f') &&
>     n == arrowArity (rawType (varType f' tyEnv)) =
>     map (merge p f ts' vs') eqs'
>   where n :: Int                      -- type signature necessary for nhc
>         (n,vs',ts',e') = etaReduce 0 [] (reverse ts) e
>         merge p f ts vs (Equation _ (FunLhs _ ts') rhs) =
>           Equation p (FunLhs f (ts ++ zipWith AsPattern vs ts')) rhs
>         etaReduce n vs (VariablePattern v : ts) (Apply e (Variable v'))
>           | qualify v == v' = etaReduce (n+1) (v:vs) ts e
>         etaReduce n vs ts e = (n,vs,reverse ts,e)
> inlineFun _ _ p lhs rhs = [Equation p lhs rhs]

> simplifyRhs :: ModuleIdent -> InlineEnv -> Rhs -> SimplifyState Rhs
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

> simplifyApp :: ModuleIdent -> Position -> Expression -> [Expression]
>             -> SimplifyState Expression
> simplifyApp _ _ (Literal l) _ = return (Literal l)
> simplifyApp _ _ (Variable v) es = return (apply (Variable v) es)
> simplifyApp _ _ (Constructor c) es = return (apply (Constructor c) es)
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
>                 return (foldr2 mkLet
>                                (Case e (map (applyToAlt (map mkVar vs)) as))
>                                vs es)
>         applyToAlt es (Alt p t rhs) = Alt p t (applyToRhs es rhs)
>         applyToRhs es (SimpleRhs p e _) = SimpleRhs p (apply e es) []
>         mkLet v e1 e2 = Let [varDecl p v e1] e2

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

> simplifyExpr :: ModuleIdent -> InlineEnv -> Expression
>              -> SimplifyState Expression
> simplifyExpr _ _ (Literal l) = return (Literal l)
> simplifyExpr m env (Variable v)
>   | isQualified v = return (Variable v)
>   | otherwise = maybe (return (Variable v)) (simplifyExpr m env)
>                       (lookupEnv (unqualify v) env)
> simplifyExpr _ _ (Constructor c) = return (Constructor c)
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

> simplifyAlt :: ModuleIdent -> InlineEnv -> Alt -> SimplifyState Alt
> simplifyAlt m env (Alt p t rhs) = liftM (Alt p t) (simplifyRhs m env rhs)

> hoistDecls :: Decl -> [Decl] -> [Decl]
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

> simplifyLet :: ModuleIdent -> InlineEnv -> [[Decl]] -> Expression
>             -> SimplifyState Expression
> simplifyLet m env [] e = simplifyExpr m env e
> simplifyLet m env (ds:dss) e =
>   do
>     ds' <- mapM (simplifyDecl m env) ds
>     tyEnv <- fetchSt
>     e' <- simplifyLet m (inlineVars tyEnv ds' env) dss e
>     dss'' <- mapM (expandPatternBindings m tyEnv (qfv m ds' ++ qfv m e')) ds'
>     return (mkLet m (concat dss'') e')

> inlineVars :: ValueEnv -> [Decl] -> InlineEnv -> InlineEnv
> inlineVars tyEnv [PatternDecl _ (VariablePattern v) (SimpleRhs _ e _)] env
>   | canInline e = bindEnv v e env
>   where canInline (Literal _) = True
>         canInline (Constructor _) = True
>         canInline (Variable v')
>           | isQualified v' = arrowArity (rawType (funType v' tyEnv)) > 0
>           | otherwise = v /= unqualify v'
>         canInline _ = False
> inlineVars _ _ env = env

> mkLet :: ModuleIdent -> [Decl] -> Expression -> Expression
> mkLet m [FreeDecl p vs] e
>   | null vs' = e
>   | otherwise = Let [FreeDecl p vs'] e
>   where vs' = filter (`elem` qfv m e) vs
> mkLet m [PatternDecl _ (VariablePattern v) (SimpleRhs _ e _)] (Variable v')
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

> simplifyMatch :: Expression -> [Alt] -> Maybe Expression
> simplifyMatch e =
>   case unapply e [] of
>     (dss,Literal l,_) -> Just . match dss (Left l)
>     (dss,Constructor c,es) -> Just . match dss (Right (c,es))
>     (_,_,_) -> const Nothing

> unapply :: Expression -> [Expression] -> ([[Decl]],Expression,[Expression])
> unapply (Literal l) es = ([],Literal l,es)
> unapply (Variable v) es = ([],Variable v,es)
> unapply (Constructor c) es = ([],Constructor c,es)
> unapply (Apply e1 e2) es = unapply e1 (e2:es)
> unapply (Let ds e) es = (ds:dss',e',es')
>   where (dss',e',es') = unapply e es
> unapply (Case e alts) es = ([],Case e alts,es)

> match :: [[Decl]] -> Either Literal (QualIdent,[Expression]) -> [Alt]
>       -> Expression
> match dss e alts =
>   head ([expr p t rhs | Alt p t rhs <- alts, t `matches` e] ++ [prelFailed])
>   where expr p t (SimpleRhs _ e' _) = foldr Let e' (dss ++ bindPattern p e t)

> matches :: ConstrTerm -> Either Literal (QualIdent,[Expression]) -> Bool
> matches (LiteralPattern l1) (Left l2) = sameLiteral l1 l2
>   where sameLiteral (Int _ i1) (Int _ i2) = i1 == i2
>         sameLiteral l1 l2 = l1 == l2
> matches (ConstructorPattern c1 _) (Right (c2,_)) = c1 == c2
> matches (VariablePattern _) _ = True
> matches (AsPattern _ t) e = matches t e

> bindPattern :: Position -> Either Literal (QualIdent,[Expression])
>             -> ConstrTerm -> [[Decl]]
> bindPattern _ (Left _) (LiteralPattern _) = []
> bindPattern p (Right (c,es)) (ConstructorPattern _ ts) =
>   [zipWith (\(VariablePattern v) e -> varDecl p v e) ts es]
> bindPattern p e (VariablePattern v) =
>   [[varDecl p v (either Literal (uncurry (apply . Constructor)) e)]]
> bindPattern p e (AsPattern v t) = bindPattern p e t ++ [[bindAs p v t]]

> bindAs :: Position -> Ident -> ConstrTerm -> Decl
> bindAs p v (LiteralPattern l) = varDecl p v (Literal l)
> bindAs p v (VariablePattern v') = varDecl p v (mkVar v')
> bindAs p v (ConstructorPattern c ts) = varDecl p v e'
>   where e' = apply (Constructor c) [mkVar v | VariablePattern v <- ts]
> bindAs p v (AsPattern v' _) = varDecl p v (mkVar v')

> prelFailed :: Expression
> prelFailed = Variable (qualifyWith preludeMIdent (mkIdent "failed"))

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

Another problem of the translation scheme is the handling of pattern
variables with higher-order types, e.g.,
\begin{verbatim}
  strange :: [a->a] -> Maybe (a->a)
  strange xs = Just x
    where (x:_) = xs
\end{verbatim}
By reusing the types of the pattern variables, the selector function
\verb|f (x:_) = x| has type \texttt{[a->a] -> a -> a} and therefore
seems to be binary function. Thus, in the goal \verb|strange []| the
selector is only applied partially and not evaluated. Note that this
goal will fail without the type annotation. In order to ensure that a
selector function is always evaluated when the corresponding variable
is used, we assume that the projection declarations -- ignoring the
additional arguments to prevent the space leak -- are actually defined
by $f_i$~$t$~\texttt{= I}~$v_i$, using a private renaming type
\begin{verbatim}
  newtype Identity a = I a
\end{verbatim}
As newtype constructors are completely transparent to the compiler,
this does not change the generated code, but only the types of the
selector functions.
\begin{verbatim}

> sharePatternRhs :: ModuleIdent -> Decl -> SimplifyState [Decl]
> sharePatternRhs m (PatternDecl p t rhs) =
>   case t of
>     VariablePattern _ -> return [PatternDecl p t rhs]
>     _ -> 
>       do
>         v <- freshVar m patternId t
>         return [PatternDecl p t (SimpleRhs p (mkVar v) []),
>                 PatternDecl p (VariablePattern v) rhs]
>   where patternId n = mkIdent ("_#pat" ++ show n)
> sharePatternRhs _ d = return [d]

> expandPatternBindings :: ModuleIdent -> ValueEnv -> [Ident] -> Decl
>                       -> SimplifyState [Decl]
> expandPatternBindings m tyEnv fvs (PatternDecl p t (SimpleRhs p' e _)) =
>   case t of
>     VariablePattern _ -> return [PatternDecl p t (SimpleRhs p' e [])]
>     _ ->
>       do
>         fs <- mapM (freshIdent m selectorId . selectorType ty) (shuffle tys)
>         return (zipWith (projectionDecl p t e) fs (shuffle vs))
>       where vs = filter (`elem` fvs) (bv t)
>             ty = typeOf tyEnv t
>             tys = map (typeOf tyEnv) vs
>             selectorType ty0 (ty:tys) =
>               polyType (foldr TypeArrow (identityType ty) (ty0:tys))
>             selectorDecl p f t (v:vs) =
>               funDecl p f (t:map VariablePattern vs) (mkVar v)
>             projectionDecl p t e f (v:vs) =
>               varDecl p v (Let [selectorDecl p f t (v:vs)]
>                                (apply (mkVar f) (e : map mkVar vs)))
> expandPatternBindings _ _ _ d = return [d]

\end{verbatim}
Auxiliary functions
\begin{verbatim}

> freshIdent :: ModuleIdent -> (Int -> Ident) -> TypeScheme
>            -> SimplifyState Ident
> freshIdent m f ty =
>   do
>     x <- liftM f (liftSt (updateSt (1 +)))
>     updateSt_ (bindFun m x ty)
>     return x

> freshVar :: Typeable a => ModuleIdent -> (Int -> Ident) -> a
>          -> SimplifyState Ident
> freshVar m f x =
>   do
>     tyEnv <- fetchSt
>     freshIdent m f (monoType (typeOf tyEnv x))

> shuffle :: [a] -> [[a]]
> shuffle xs = shuffle id xs
>   where shuffle _ [] = []
>         shuffle f (x:xs) = (x : f xs) : shuffle (f . (x:)) xs

> apply :: Expression -> [Expression] -> Expression
> apply = foldl Apply

> mkVar :: Ident -> Expression
> mkVar = Variable . qualify

> varDecl :: Position -> Ident -> Expression -> Decl
> varDecl p v e = PatternDecl p (VariablePattern v) (SimpleRhs p e [])

> funDecl :: Position -> Ident -> [ConstrTerm] -> Expression -> Decl
> funDecl p f ts e =
>   FunctionDecl p f [Equation p (FunLhs f ts) (SimpleRhs p e [])]

> identityType :: Type -> Type
> identityType = TypeConstructor qIdentityId . return
>   where qIdentityId = qualify (mkIdent "Identity")

\end{verbatim}
