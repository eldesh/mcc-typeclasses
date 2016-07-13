% -*- LaTeX -*-
% $Id: PatternBind.lhs 3273 2016-07-13 21:23:01Z wlux $
%
% Copyright (c) 2003-2016, Wolfgang Lux
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
  of encapsulated search in Curry.} Our transformation, which is
explained below, uses two new primitives \texttt{pbUpdate} and
\texttt{pbReturn} and foreign function declarations for them are added
to the program when necessary. In order to detect when adding these
declarations is necessary, we simply check whether any fresh variables
were introduced in the code by the transformation.
\begin{verbatim}

> module PatternBind(pbTrans) where
> import Base
> import Combined
> import Curry
> import CurryUtils
> import List
> import Monad
> import Position
> import PredefIdent
> import PredefTypes
> import Types
> import TypeTrans
> import Typing
> import ValueInfo

> type PatternBindState a = StateT Int Id a

> pbTrans :: ValueEnv -> Module QualType -> (ValueEnv,Module QualType)
> pbTrans tyEnv m = runSt (pbtModule tyEnv m) 1

> pbtModule :: ValueEnv -> Module QualType
>           -> PatternBindState (ValueEnv,Module QualType)
> pbtModule tyEnv (Module m es is ds) =
>   do
>     n <- fetchSt
>     ds' <- mapM (pbt m) ds
>     n' <- fetchSt
>     let ap = if n == n' then const id else ($)
>     return (ap bindPrims tyEnv,Module m es is (ap (prims ++) ds'))
>   where noPos = internalError "pbtModule: no position"
>         Variable tyUpd pbUpd = pbUpdate m (TypeVariable 0)
>         Variable tyRet pbRet = pbReturn m (TypeVariable 0)
>         bindPrims = bindForeign pbUpd tyUpd . bindForeign pbRet tyRet
>         prims =
>           [BlockDecl (foreignDecl noPos "pbUpdate" pbUpd tyUpd),
>            BlockDecl (foreignDecl noPos "pbReturn" pbRet tyRet)]

> class SyntaxTree a where
>   pbt :: ModuleIdent -> a QualType -> PatternBindState (a QualType)

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

> instance SyntaxTree Decl where
>   pbt m (FunctionDecl p ty f eqs) =
>     liftM (FunctionDecl p ty f) (mapM (pbt m) eqs)
>   pbt _ (ForeignDecl p fi ty f ty') = return (ForeignDecl p fi ty f ty')
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
>   pbt m (Tuple es) = liftM Tuple (mapM (pbt m) es)
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
functions for a pattern binding has been evaluated, we introduce an
auxiliary constraint function that matches the pattern with the right
hand side expression of the declaration and then updates \emph{all}
pattern variables. The selector function for each pattern variable
first evaluates the shared constraint and then returns the respective
pattern component. Recall that case matching transforms each pattern
declaration of the form $t$~\texttt{=}~$e$, where $t$ is not a
variable pattern, into an equation
\begin{center}
  \begin{tabular}{l}
    \texttt{$(v_1,\dots,v_n)$ = fcase $e$ of \lb{} $t'_1$ -> $\dots$
      fcase $u_k$ of \lb{} $t'_k$ -> $(v_1,\dots,v_n)$ \rb{}$\dots$\rb{}},
  \end{tabular}
\end{center}
where $v_1,\dots,v_n$ are the free variables of $t$, the patterns
$t'_1,\dots,t'_k$ are flat patterns using fresh variables, and
$u_2,\dots,u_k$ are variables occurring in these patterns such that
the right hand side of the equation matches the same pattern as $t$.
Also recall that the simplifier reduces the tuples $(v_1,\dots,v_n)$
to those variables which are actually used in the scope of the
declaration. Each such equation is now transformed by
\texttt{expandPatternBindings} into a list of equations
\begin{center}\tt
  \begin{tabular}{rcl}
    $v_0$ & = & fcase $e$ of \lb{} $t'_1$ -> $\dots$
      fcase $u_k$ of \lb{} $t'_k$ -> $e'$ \rb{}$\dots$\rb{} \\
          &   & \textrm{where $e' =$
                        \texttt{pbUpdate $v_1$ $v'_1$ \&> $\dots$ \&>
                                pbUpdate $v_n$ $v'_n$}} \\
    $v_1$ & = & pbReturn $v_0$ $v_1$ \\
    \multicolumn{3}{l}{\dots} \\
    $v_n$ & = & pbReturn $v_0$ $v_n$ \\
  \end{tabular}
\end{center}
where $v_0$ is a fresh variable and $v'_1,\dots,v'_n$ are variables
from $t'_1,\dots,t'_k$ that match the same components as
$v_1,\dots,v_n$, respectively, in $t$. Each application
\texttt{pbUpdate $v_i$ $v'_i$} updates the lazy application node bound
to $v_i$ with the pattern component bound to $v'_i$. An application
\texttt{pbReturn $v_0$ $v_i$} is evaluated similar to \texttt{$v_0$
  \&> $v_i$}, but \texttt{pbReturn} is prepared to handle the fact
that the lazy application bound to $v_i$ is already updated by the
constraint $v_0$.
\begin{verbatim}

> expandPatternBindings :: ModuleIdent -> [Ident] -> Decl QualType
>                       -> PatternBindState [Decl QualType]
> expandPatternBindings m fvs (PatternDecl p t rhs) =
>   case (t,rhs) of
>     (VariablePattern _ _,_) -> return [PatternDecl p t rhs]
>     (TuplePattern ts,SimpleRhs _ e _) ->
>       do
>         v0 <- freshVar "_#pbt" boolType
>         return (updateDecl m p v0 vs e :
>                 map (selectorDecl m p (uncurry mkVar v0)) vs)
>       where vs = [(ty,v) | VariablePattern ty v <- ts]
> expandPatternBindings _ _ d = return [d]

> updateDecl :: ModuleIdent -> Position -> (QualType,Ident)
>            -> [(QualType,Ident)] -> Expression QualType -> Decl QualType
> updateDecl m p v0 vs e = uncurry (varDecl p) v0 (fixBody vs e)
>   where fixBody vs (Tuple es) = foldr1 (cond p) (zipWith (update m) vs es)
>         fixBody vs (Let ds e) = Let ds (fixBody vs e)
>         fixBody vs (Case e [Alt p t rhs]) = Case e [Alt p t (fixRhs vs rhs)]
>         fixBody vs (Fcase e [Alt p t rhs]) = Fcase e [Alt p t (fixRhs vs rhs)]
>         fixRhs vs (SimpleRhs p e _) = SimpleRhs p (fixBody vs e) []

> cond :: Position -> Expression QualType -> Expression QualType
>      -> Expression QualType
> cond p c e = Case c [caseAlt p truePattern e]
>   where truePattern = ConstructorPattern qualBoolType qTrueId []

> update :: ModuleIdent -> (QualType,Ident) -> Expression QualType
>        -> Expression QualType
> update m v = Apply (Apply (pbUpdate m (unqualType (fst v))) (uncurry mkVar v))

> selectorDecl :: ModuleIdent -> Position -> Expression QualType
>              -> (QualType,Ident) -> Decl QualType
> selectorDecl m p e v = uncurry (varDecl p) v (ret m e v)

> ret :: ModuleIdent -> Expression QualType -> (QualType,Ident)
>     -> Expression QualType
> ret m e v = apply (pbReturn m (unqualType (fst v))) [e,uncurry mkVar v]

\end{verbatim}
Pattern binding primitives.
\begin{verbatim}

> pbUpdate, pbReturn :: ModuleIdent -> Type -> Expression QualType
> pbUpdate m ty = pbFun m [ty,ty] boolType "_#update"
> pbReturn m ty = pbFun m [boolType,ty] ty "_#return"

> pbFun :: ModuleIdent -> [Type] -> Type -> String -> Expression QualType
> pbFun m tys ty f =
>   Variable (qualType (foldr TypeArrow ty tys)) (qualifyWith m (mkIdent f))

\end{verbatim}
Generation of fresh names.
\begin{verbatim}

> freshVar :: String -> Type -> PatternBindState (QualType,Ident)
> freshVar prefix ty =
>   do
>     v <- liftM mkName (updateSt (1 +))
>     return (qualType ty,v)
>   where mkName n = renameIdent (mkIdent (prefix ++ show n)) n

\end{verbatim}
Auxiliary functions.
\begin{verbatim}

> foreignDecl :: Position -> String -> QualIdent -> QualType -> Decl QualType
> foreignDecl p ie f ty =
>   ForeignDecl p (CallConvPrimitive,Just Safe,Just ie) ty (unqualify f)
>               (fromType nameSupply (unqualType ty))

> bindForeign :: QualIdent -> QualType -> ValueEnv -> ValueEnv
> bindForeign f ty = bindFun m f' (arrowArity (unqualType ty)) (typeScheme ty)
>   where (Just m,f') = splitQualIdent f

\end{verbatim}
