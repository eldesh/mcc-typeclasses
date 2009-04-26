% -*- LaTeX -*-
% $Id: PatternBind.lhs 2803 2009-04-26 17:14:20Z wlux $
%
% Copyright (c) 2003-2009, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{PatternBind.lhs}
\section{Pattern Binding Updates}\label{sec:pattern-bindings}
The standard implementation of pattern bindings for local declarations
transforms each pattern declaration $t$~\texttt{=}~$e$, where $t$ is
not a variable pattern, into a list of declarations
$v_0$~\texttt{=}~$e$\texttt{;} $v_1$~\texttt{=}~$f_1$~$v_0$\texttt{;}
\dots{} \texttt{;} $v_n$~\texttt{=}~$f_n$~$v_0$ where $v_0$ is a fresh
variable, $v_1,\dots,v_n$ are the variables occurring in $t$ and the
auxiliary functions $f_i$ are defined by $f_i$~$t$~\texttt{=}~$v_i$
(see also appendix D.8 of the Curry report~\cite{Hanus:Report}).
Unfortunately, this transformation introduces a well-known space
leak~\cite{Wadler87:Leaks,Sparud93:Leaks}, since the matched
expression cannot be garbage collected before all of the matched
variables have been evaluated. Consider the following function:
\begin{verbatim}
  f x | all (' ' ==) cs = c where (c:cs) = x
\end{verbatim}
One might expect the call \verb|f (replicate 10000 ' ')| to execute in
constant space because (the tail of) the long list of blanks is
consumed and discarded immediately by \texttt{all}. However, the
application of the selector function that extracts the head of the
list is not evaluated until after the guard succeeds and thus prevents
the whole list from being garbage collected. In order to avoid this
space leak we use the approach from~\cite{Sparud93:Leaks} and update
all pattern variables when one of the components is
evaluated.\footnote{We do not attempt to fix the space leak with the
  garbage collector~\cite{Wadler87:Leaks} because the updates may have
  to be undone when executed in non-deterministic code. Detecting when
  recording an update is necessary, and in particular where to record
  it, is quite difficult for the garbage collector due to the presence
  of encapsulated search in Curry.}
\begin{verbatim}

> module PatternBind(pbTrans) where
> import Base
> import Combined
> import Curry
> import CurryUtils
> import List
> import Monad
> import PredefIdent
> import Types
> import Typing
> import ValueInfo

> type PatternBindState a = StateT ValueEnv (StateT Int Id) a

> pbTrans :: ValueEnv -> Module Type -> (Module Type,ValueEnv)
> pbTrans tyEnv m = runSt (callSt (pbtModule m) tyEnv) 1

> pbtModule :: Module Type -> PatternBindState (Module Type,ValueEnv)
> pbtModule (Module m es is ds) =
>   do
>     ds' <- mapM (pbt m) ds
>     tyEnv <- fetchSt
>     return (Module m es is ds',tyEnv)

> class SyntaxTree a where
>   pbt :: ModuleIdent -> a Type -> PatternBindState (a Type)

> instance SyntaxTree TopDecl where
>   pbt _ (DataDecl p cx tc tvs cs clss) = return (DataDecl p cx tc tvs cs clss)
>   pbt _ (NewtypeDecl p cx tc tvs nc clss) =
>     return (NewtypeDecl p cx tc tvs nc clss)
>   pbt _ (TypeDecl p tc tvs ty) = return (TypeDecl p tc tvs ty)
>   pbt m (ClassDecl p cx cls tv ds) =
>     liftM (ClassDecl p cx cls tv . (tds ++)) (mapM (pbt m) vds)
>     where (tds,vds) = partition isTypeSig ds
>   pbt m (InstanceDecl p cx cls ty ds) =
>     liftM (InstanceDecl p cx cls ty) (mapM (pbt m) ds)
>   pbt _ (DefaultDecl p tys) = return (DefaultDecl p tys)
>   pbt m (BlockDecl d) = liftM BlockDecl (pbt m d)
>   pbt _ (SplitAnnot p) = return (SplitAnnot p)

> instance SyntaxTree Decl where
>   pbt m (FunctionDecl p f eqs) = liftM (FunctionDecl p f) (mapM (pbt m) eqs)
>   pbt _ (ForeignDecl p cc s ie f ty) = return (ForeignDecl p cc s ie f ty)
>   pbt m (PatternDecl p t rhs) = liftM (PatternDecl p t) (pbt m rhs)
>   pbt _ (FreeDecl p vs) = return (FreeDecl p vs)

> instance SyntaxTree Equation where
>   pbt m (Equation p lhs rhs) = liftM (Equation p lhs) (pbt m rhs)

> instance SyntaxTree Rhs where
>   pbt m (SimpleRhs p e _) = liftM (flip (SimpleRhs p) []) (pbt m e)

> instance SyntaxTree Expression where
>   pbt _ (Literal ty l) = return (Literal ty l)
>   pbt _ (Variable ty v) = return (Variable ty v)
>   pbt _ (Constructor ty c) = return (Constructor ty c)
>   pbt m (Apply e1 e2) = liftM2 Apply (pbt m e1) (pbt m e2)
>   pbt m (Lambda p ts e) = liftM (Lambda p ts) (pbt m e)
>   pbt m (Let ds e) = liftM2 (Let . concat) (mapM (pbtDecl m) ds) (pbt m e)
>     where fvs = qfv m ds ++ qfv m e
>           pbtDecl m d = pbt m d >>= expandPatternBindings m fvs
>   pbt m (Case e as) = liftM2 Case (pbt m e) (mapM (pbt m) as)
>   pbt m (Fcase e as) = liftM2 Fcase (pbt m e) (mapM (pbt m) as)

> instance SyntaxTree Alt where
>   pbt m (Alt p t rhs) = liftM (Alt p t) (pbt m rhs)

\end{verbatim}
In order to update all pattern variables when one of the selector
functions for a pattern binding has been evaluated, we pass all
pattern variables except for the matched one as additional arguments
to each selector function. Recall that case matching transforms
pattern declarations of the form $t$~\texttt{=}~$e$ into a
(pseudo-)\discretionary{}{}{}flattened form $t$~\texttt{=}
\texttt{fcase}~$e$~\texttt{of} \texttt{\char`\{}~$\dots{}\rightarrow
t$~\texttt{\char`\}}, where the nested \texttt{fcase} expressions on
the right hand side contain only flat patterns. The transformation
into abstract machine code (see Sect.~\ref{sec:il-compile}) transforms
selector functions, which are identified by their distinguished names,
specially, inserting code that updates each of the additional
arguments from the pattern variable with the same name once the
pattern has been matched successfully in the body of the fcase
expression.

\ToDo{Get rid of the obscure dependence on name equivalence between
  the auxiliary arguments and the corresponding pattern variables.}

Note that we introduce only selector functions for those pattern
variables which are actually used in the code. This reduces the number
of auxiliary variables and prevents the introduction of a recursive
binding group when only a single variable is used. This is the reason
for performing this transformation after simplification instead of
during case matching.
\begin{verbatim}

> expandPatternBindings :: ModuleIdent -> [Ident] -> Decl Type
>                       -> PatternBindState [Decl Type]
> expandPatternBindings m fvs (PatternDecl p t rhs) =
>   case (t,rhs) of
>     (VariablePattern _ _,_) -> return [PatternDecl p t rhs]
>     (_,SimpleRhs _ e@(Fcase (Variable ty v) _) _) ->
>       mapM (projectionDecl m p v0 e) (shuffle vs)
>       where vs = filter ((`elem` fvs) . snd) (vars t)
>             v0 = (ty,unqualify v)
> expandPatternBindings _ _ d = return [d]

> projectionDecl :: ModuleIdent -> Position -> (Type,Ident) -> Expression Type
>                -> [(Type,Ident)] -> PatternBindState (Decl Type)
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
Generation of fresh names.
\begin{verbatim}

> freshIdent :: ModuleIdent -> (Int -> Ident) -> Int -> TypeScheme
>            -> PatternBindState Ident
> freshIdent m f n ty =
>   do
>     x <- liftM f (liftSt (updateSt (1 +)))
>     updateSt_ (bindFun m x n ty)
>     return x

> freshVar :: Typeable a => ModuleIdent -> (Int -> Ident) -> a
>          -> PatternBindState (Type,Ident)
> freshVar m f x =
>   do
>     v <- freshIdent m f 0 (monoType ty)
>     return (ty,v)
>   where ty = typeOf x

\end{verbatim}
Auxiliary functions.
\begin{verbatim}

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
