% -*- LaTeX -*-
% $Id: CaseMatch.lhs 2807 2009-04-26 17:36:12Z wlux $
%
% Copyright (c) 2001-2009, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CaseMatch.lhs}
\section{Flattening Patterns}\label{sec:flatcase}
After desugaring source code, the compiler makes pattern matching in
equations, lambda abstractions, and $($f$)$case expressions fully
explicit by restricting pattern matching to $($f$)$case expressions
with only flat patterns. This means that the compiler transforms the
code in such way that all functions have only a single equation,
equations and lambda abstractions have only variable arguments,xs and
all patterns in $($f$)$case expressions are of the form $l$, $v$,
$C\,v_1\dots v_n$, or $v\texttt{@}(C\,v_1\dots v_n)$ where $l$ is a
literal, $v$ and $v_1, \dots, v_n$ are variables, and $C$ is a data
constructor.\footnote{Recall that all newtype constructors have been
  removed previously.} During this transformation, the compiler also
replaces (boolean) guards by if-then-else cascades and changes
if-then-else expressions into equivalent case expressions.
\begin{verbatim}

> module CaseMatch(caseMatch) where
> import Base
> import Combined
> import Curry
> import CurryUtils
> import List
> import Monad
> import PredefIdent
> import PredefTypes
> import Types
> import TypeInfo
> import Typing
> import Utils
> import ValueInfo

\end{verbatim}
New identifiers are introduced to replace subterms of nested patterns.
As usual, we use a state monad transformer for generating unique
names. In addition, the state is also used for passing through the
type environment, which is augmented with the types of the new
variables.
\begin{verbatim}

> type CaseMatchState a = StateT ValueEnv (ReaderT TCEnv (StateT Int Id)) a

> run :: CaseMatchState a -> TCEnv -> ValueEnv -> a
> run m tcEnv tyEnv = runSt (callRt (callSt m tyEnv) tcEnv) 1

\end{verbatim}
The case flattening phase is applied recursively to all declarations
and expressions of the desugared source code. A special case is made
for pattern declarations. Since we cannot flatten the left hand side
of a pattern declaration $t$~\texttt{=}~$e$, where $t$ is not a
variable pattern, it is first transformed into the form
$(v_1,\dots,v_n)$~\texttt{=} \texttt{fcase}~$e$ \texttt{of}
\texttt{\lb}~$\sigma(t) \rightarrow (v'_1,\dots,v'_n)$~\texttt{\rb},
where $v_1,\dots,v_n$ are the variables occurring in $t$,
$v'_1,\dots,v'_n$ are fresh variables, and the substitution $\sigma =
\{ v_1 \mapsto v'_1, \dots, v_n \mapsto v'_n \}$. Now $t$ can be
flattened on the right hand side of the declaration. After
simplification, the compiler will replace the transformed pattern
declaration by individual declarations for those variables from
$\{v_1,\dots,v_n\}$ that are used in the scope of the declaration
using a space-leak avoiding transformation of pattern bindings (cf.\ 
Sect.~\ref{sec:pattern-bindings}).

Note that we make deliberate use of the tuple syntax for the pattern
on the left hand side of the transformed declaration and the body of
the fcase expression on its right hand side. This makes it easier to
determine the variables of the pattern and to handle optimizations on
the right hand side of the declaration during later phases of the
compiler. Also note that pattern declarations with only a single
variable automatically degenerate into normal variable declarations.
For instance, \texttt{Just x = unknown} becomes \texttt{x = fcase
  unknown of \lb{} Just a1 -> a1 \rb{}}.
\begin{verbatim}

> caseMatch :: TCEnv -> ValueEnv -> Module Type -> (Module Type,ValueEnv)
> caseMatch tcEnv tyEnv (Module m es is ds) = (Module m es is ds',tyEnv')
>   where (ds',tyEnv') = run (caseMatchModule m ds) tcEnv tyEnv

> caseMatchModule :: ModuleIdent -> [TopDecl Type]
>                 -> CaseMatchState ([TopDecl Type],ValueEnv)
> caseMatchModule m ds =
>   do
>     ds' <- mapM (match m noPos) ds
>     tyEnv' <- fetchSt
>     return (ds',tyEnv')
>   where noPos = internalError "caseMatch: no position"

> class CaseMatch a where
>   match :: ModuleIdent -> Position -> a Type -> CaseMatchState (a Type)

> instance CaseMatch TopDecl where
>   match _ _ (DataDecl p cx tc tvs cs clss) =
>     return (DataDecl p cx tc tvs cs clss)
>   match _ _ (NewtypeDecl p cx tc tvs nc clss) =
>     return (NewtypeDecl p cx tc tvs nc clss)
>   match _ _ (TypeDecl p tc tvs ty) = return (TypeDecl p tc tvs ty)
>   match m _ (ClassDecl p cx cls tv ds) =
>     liftM (ClassDecl p cx cls tv) (mapM (match m p) ds)
>   match m _ (InstanceDecl p cx cls ty ds) =
>     liftM (InstanceDecl p cx cls ty) (mapM (match m p) ds)
>   match _ _ (DefaultDecl p tys) = return (DefaultDecl p tys)
>   match m p (BlockDecl d) = liftM BlockDecl (match m p d)
>   match _ _ (SplitAnnot p) = return (SplitAnnot p)

> instance CaseMatch Decl where
>   match _ _ (InfixDecl p fix pr ops) = return (InfixDecl p fix pr ops)
>   match _ _ (TypeSig p fs ty) = return (TypeSig p fs ty)
>   match m _ (FunctionDecl p f eqs) =
>     do
>       vs <- matchVars m (map snd3 as)
>       e <- flexMatch m p vs as
>       return (funDecl p f (map (uncurry VariablePattern) vs) e)
>     where as = [(p,ts,rhs) | Equation p (FunLhs _ ts) rhs <- eqs]
>   match _ _ (ForeignDecl p cc s ie f ty) = return (ForeignDecl p cc s ie f ty)
>   match m _ (PatternDecl p t rhs) =
>     match m p rhs >>= liftM (uncurry (PatternDecl p)) . matchLhs m t
>   match _ _ (FreeDecl p vs) = return (FreeDecl p vs)
>   match _ _ (TrustAnnot p tr fs) = return (TrustAnnot p tr fs)

> matchLhs :: ModuleIdent -> ConstrTerm Type -> Rhs Type
>          -> CaseMatchState (ConstrTerm Type,Rhs Type)
> matchLhs m t (SimpleRhs p e _)
>   | isVarPattern t = return (t,mkRhs p e)
>   | otherwise =
>       do
>         vs' <- mapM (freshVar m "_#case" . fst) vs
>         let t' = rename (zip (map snd vs) (map snd vs')) t
>         [v] <- matchVars m [[t']]
>         Fcase _ as' <- flexMatch m p [v] [(p,[t'],mkRhs p (tupleExpr vs'))]
>         return (tuplePattern vs,mkRhs p (Fcase e as'))
>   where vs = vars t
>         rename _ (LiteralPattern ty l) = LiteralPattern ty l
>         rename vs (VariablePattern ty v) = VariablePattern ty (renameVar vs v)
>         rename vs (ConstructorPattern ty c ts) =
>           ConstructorPattern ty c (map (rename vs) ts)
>         rename vs (AsPattern v t) = AsPattern (renameVar vs v) (rename vs t)
>         renameVar vs v = maybe v id (lookup v vs)

\end{verbatim}
A list of boolean guards is expanded into a nested if-then-else
expression, whereas a constraint guard is replaced by a case
expression. Note that if the guard type is \texttt{Success} only a
single guard is allowed for each equation. We check whether the
guard's type is \texttt{Bool} because it defaults to \texttt{Success}
if it is not restricted by the guard expression.
\begin{verbatim}

> instance CaseMatch Rhs where
>   match m p rhs = liftM (mkRhs p) (matchRhs m p rhs (prelFailed (typeOf rhs)))

> matchRhs :: ModuleIdent -> Position -> Rhs Type -> Expression Type
>          -> CaseMatchState (Expression Type)
> matchRhs m p rhs e0 = match m p (expandRhs e0 rhs)

> expandRhs :: Expression Type -> Rhs Type -> Expression Type
> expandRhs _ (SimpleRhs _ e ds) = mkLet ds e
> expandRhs e0 (GuardedRhs es ds) = mkLet ds (expandGuards e0 es)

> expandGuards :: Expression Type -> [CondExpr Type] -> Expression Type
> expandGuards e0 es
>   | booleanGuards es = foldr mkIfThenElse e0 es
>   | otherwise = mkCase es
>   where mkIfThenElse (CondExpr _ g e) = IfThenElse g e
>         mkCase [CondExpr p g e] = Case g [caseAlt p successPattern e]

> booleanGuards :: [CondExpr Type] -> Bool
> booleanGuards [] = False
> booleanGuards (CondExpr _ g _ : es) = not (null es) || typeOf g == boolType

> instance CaseMatch Expression where
>   match _ _ (Literal ty l) = return (Literal ty l)
>   match _ _ (Variable ty v) = return (Variable ty v)
>   match _ _ (Constructor ty c) = return (Constructor ty c)
>   match _ _ (Tuple vs) = return (Tuple vs)
>   match m p (Apply e1 e2) = liftM2 Apply (match m p e1) (match m p e2)
>   match m _ (Lambda p ts e) =
>     do
>       vs <- matchVars m [ts]
>       e' <- flexMatch m p vs [(p,ts,mkRhs p e)]
>       return (Lambda p (map (uncurry VariablePattern) vs) e')
>   match m p (Let ds e) = liftM2 Let (mapM (match m p) ds) (match m p e)
>   match m p (IfThenElse e1 e2 e3) =
>     liftM3 mkCase (match m p e1) (match m p e2) (match m p e3)
>     where mkCase e1 e2 e3 =
>             Case e1 [caseAlt p truePattern e2,caseAlt p falsePattern e3]
>   match m p (Case e as) =
>     do
>       e' <- match m p e
>       [v] <- matchVars m [ts | (_,_,ts,_) <- as']
>       liftM (mkCase m p v e') (rigidMatch m (typeOf (Case e as)) id [v] as')
>     where as' = [(p,id,[t],rhs) | Alt p t rhs <- as]
>   match m p (Fcase e as) =
>     do
>       e' <- match m p e
>       [v] <- matchVars m (map snd3 as')
>       liftM (mkCase m p v e') (flexMatch m p [v] as')
>     where as' = [(p,[t],rhs) | Alt p t rhs <- as]

> instance CaseMatch Alt where
>   match m _ (Alt p t rhs) = liftM (Alt p t) (match m p rhs)

\end{verbatim}
Our pattern matching algorithm is based on the notions of demanded and
inductive positions defined in Sect.~D.5 of the Curry
report~\cite{Hanus:Report}. Given a list of terms, a demanded position
is a position where a constructor rooted term occurs in at least one
of the terms. An inductive position is a position where a constructor
rooted term occurs in each of the terms. Obviously, every inductive
position is also a demanded position. For the purpose of pattern
matching we treat literal terms as constructor rooted terms.

The algorithm looks for the leftmost outermost inductive argument
position in the left hand sides of all rules defining an equation. If
such a position is found, a fcase expression is generated for the
argument at that position. The matching algorithm is then applied
recursively to each of the alternatives at that position. If no
inductive position is found, the algorithm looks for the leftmost
outermost demanded argument position. If such a position is found, a
choice expression with two alternatives is generated, one for rules
with a variable at the demanded position, and one for the rules with a
constructor rooted term at that position. If there is no demanded
position either, pattern matching is complete and the compiler
translates the right hand sides of the remaining rules, eventually
combining them into a non-deterministic choice.

In fact, the algorithm combines the search for inductive and demanded
positions. The function \texttt{flexMatch} scans the argument lists for
the leftmost demanded position. If this turns out to be also an
inductive position, the function \texttt{matchInductive} is called in
order to generate a \texttt{fcase} expression. Otherwise, the function
\texttt{optMatch} is called that looks for an inductive position among
the remaining arguments. If one is found, \texttt{matchInductive} is
called for that position, otherwise the function \texttt{optMatch}
uses the demanded argument position found by \texttt{flexMatch}.

Since our Curry representation does not include non-deterministic
choice expressions, we encode them as flexible case expressions
matching an auxiliary free variable~\cite{AntoyHanus06:Overlapping}.
For instance, an expression equivalent to $e_1$~\texttt{?}~$e_2$ is
represented as
\begin{quote}\tt
  fcase (let x free in x) of \lb{} 1 -> $e_1$; 2 -> $e_2$ \rb{}
\end{quote}

Note that the function \texttt{matchVars} attempts to avoid
introducing fresh variables for variable patterns already present in
the source code when there is only a single alternative in order to
make the result of the transformation easier to check and more
comprehensible.
\begin{verbatim}

> type Match a = (Position,[ConstrTerm a],Rhs a)
> type Match' a =
>   (Position,[ConstrTerm a] -> [ConstrTerm a],[ConstrTerm a],Rhs a)

> pattern :: ConstrTerm a -> ConstrTerm ()
> pattern (LiteralPattern _ l) = LiteralPattern () l
> pattern (VariablePattern _ _) = VariablePattern () anonId
> pattern (ConstructorPattern _ c ts) =
>   ConstructorPattern () c (map (const (VariablePattern () anonId)) ts)
> pattern (AsPattern _ t) = pattern t

> arguments :: ConstrTerm a -> [ConstrTerm a]
> arguments (LiteralPattern _ _) = []
> arguments (VariablePattern _ _) = []
> arguments (ConstructorPattern _ _ ts) = ts
> arguments (AsPattern _ t) = arguments t

> bindVars :: Position -> Ident -> ConstrTerm Type -> Rhs Type -> Rhs Type
> bindVars _ _ (LiteralPattern _ _) = id
> bindVars p v' (VariablePattern ty v) = bindVar p ty v v'
> bindVars _ _ (ConstructorPattern _ _ _) = id
> bindVars p v' (AsPattern v t) = bindVar p (typeOf t) v v' . bindVars p v' t

> bindVar :: Position -> a -> Ident -> Ident -> Rhs a -> Rhs a
> bindVar p ty v v'
>   | v /= v' = addDecl (varDecl p ty v (mkVar ty v'))
>   | otherwise = id

> flexMatch :: ModuleIdent -> Position -> [(Type,Ident)] -> [Match Type]
>           -> CaseMatchState (Expression Type)
> flexMatch m p []     as = mapM (match m p . thd3) as >>= matchChoice m p
> flexMatch m p (v:vs) as
>   | null vars = e1
>   | null nonVars = e2
>   | otherwise =
>       optMatch m (join (liftM2 (matchOr m p) e1 e2)) (v:) vs (map skipArg as)
>   where (vars,nonVars) = partition (isVarPattern . fst) (map tagAlt as)
>         e1 = matchInductive m id v vs nonVars
>         e2 = flexMatch m p vs (map (matchVar . snd) vars)
>         tagAlt (p,t:ts,rhs) = (pattern t,(p,id,t:ts,rhs))
>         skipArg (p,t:ts,rhs) = (p,(t:),ts,rhs)
>         matchVar (p,_,t:ts,rhs) = (p,ts,bindVars p (snd v) t rhs)

> optMatch :: ModuleIdent -> CaseMatchState (Expression Type)
>          -> ([(Type,Ident)] -> [(Type,Ident)]) -> [(Type,Ident)]
>          -> [Match' Type] -> CaseMatchState (Expression Type)
> optMatch _ e _      []     _ = e
> optMatch m e prefix (v:vs) as
>   | null vars = matchInductive m prefix v vs nonVars
>   | otherwise = optMatch m e (prefix . (v:)) vs (map skipArg as)
>   where (vars,nonVars) = partition (isVarPattern . fst) (map tagAlt as)
>         tagAlt (p,prefix,t:ts,rhs) = (pattern t,(p,prefix,t:ts,rhs))
>         skipArg (p,prefix,t:ts,rhs) = (p,prefix . (t:),ts,rhs)

> matchInductive :: ModuleIdent -> ([(Type,Ident)] -> [(Type,Ident)])
>                -> (Type,Ident) -> [(Type,Ident)]
>                -> [(ConstrTerm (),Match' Type)]
>                -> CaseMatchState (Expression Type)
> matchInductive m prefix v vs as =
>   liftM (Fcase (uncurry mkVar v)) (matchAlts m prefix v vs as)

> matchChoice :: ModuleIdent -> Position -> [Rhs Type]
>             -> CaseMatchState (Expression Type)
> matchChoice m p (rhs:rhss)
>   | null rhss = return (expr rhs)
>   | otherwise =
>       do
>         v <- freshVar m "_#choice" (head ts)
>         return (Fcase (freeVar p v) (zipWith (Alt p) ts (rhs:rhss)))
>   where ts = map (LiteralPattern intType . Integer) [0..]
>         freeVar p v = Let [FreeDecl p [snd v]] (uncurry mkVar v)
>         expr (SimpleRhs _ e _) = e

> matchOr :: ModuleIdent -> Position -> Expression Type -> Expression Type
>         -> CaseMatchState (Expression Type)
> matchOr m p e1 e2 = matchChoice m p [mkRhs p e1,mkRhs p e2]

> matchAlts :: ModuleIdent -> ([(Type,Ident)] -> [(Type,Ident)]) -> (Type,Ident)
>           -> [(Type,Ident)] -> [(ConstrTerm (),Match' Type)]
>           -> CaseMatchState [Alt Type]
> matchAlts _ _      _ _  [] = return []
> matchAlts m prefix v vs ((t,a):as) =
>   do
>     a' <- matchAlt m prefix v vs (a : map snd same) 
>     as' <- matchAlts m prefix v vs others
>     return (a' : as')
>   where (same,others) = partition ((t ==) . fst) as

> matchAlt :: ModuleIdent -> ([(Type,Ident)] -> [(Type,Ident)]) -> (Type,Ident)
>          -> [(Type,Ident)] -> [Match' Type] -> CaseMatchState (Alt Type)
> matchAlt m prefix v vs as@((p,_,t:_,_) : _) =
>   do
>     vs' <- matchVars m [arguments t | (_,_,t:_,_) <- as]
>     e' <- flexMatch m p (prefix (vs' ++ vs)) (map expandArg as)
>     return (caseAlt p (renameArgs (snd v) vs' t) e')
>   where expandArg (p,prefix,t:ts,rhs) =
>           (p,prefix (arguments t ++ ts),bindVars p (snd v) t rhs)

> matchVars :: ModuleIdent -> [[ConstrTerm Type]]
>           -> CaseMatchState [(Type,Ident)]
> matchVars m tss = mapM argName (transpose tss)
>   where argName [VariablePattern ty v] = return (ty,v)
>         argName [AsPattern v t] = return (typeOf t,v)
>         argName (t:_) = freshVar m "_#case" t

> renameArgs :: Ident -> [(a,Ident)] -> ConstrTerm a -> ConstrTerm a
> renameArgs v _ (LiteralPattern ty l) = AsPattern v (LiteralPattern ty l)
> renameArgs v _ (VariablePattern ty _) = VariablePattern ty v
> renameArgs v vs (ConstructorPattern ty c _) =
>   AsPattern v (ConstructorPattern ty c (map (uncurry VariablePattern) vs))
> renameArgs v vs (AsPattern _ t) = renameArgs v vs t

\end{verbatim}
The algorithm used for rigid case expressions is a variant of the
algorithm used above for transforming pattern matching of function
heads and flexible case expressions. In contrast to the algorithm
presented in Sect.~5 of~\cite{PeytonJones87:Book}, the code generated
by our algorithm will not perform redundant matches. Furthermore, we
do not need a special pattern match failure primitive and fatbar
expressions in order to catch such failures. On the other hand, our
algorithm can cause code duplication. We do not care about that
because most pattern matching in Curry programs occurs in function
heads and not in case expressions.

The essential difference between pattern matching in rigid case
expressions on one hand and function heads and flexible fcase
expressions on the other hand is that in case expressions,
alternatives are matched from top to bottom and evaluation commits to
the first alternative with a matching pattern. If an alternative uses
boolean guards and all guards of that alternative fail, pattern
matching continues with the next alternative as if the pattern did not
match. As an extension, we also support constraint guards, but do not
fall through to the remaining alternatives if the guard fails, since
this cannot be implemented without negation of constraints. For
instance, the expression
\begin{verbatim}
  case x of
    Left y | y >= 0 -> 1
    Right z | z =/= 0.0 -> 2
    _ -> 3
\end{verbatim}
reduces to 3 if \texttt{x} is bound to an application of \texttt{Left}
to a negative number because pattern matching continues when the
boolean guard \texttt{y >= 0} reduces to \texttt{False}. On the other
hand, the case expression does not reduce to 3 if \texttt{x} is bound
to \texttt{Right 0.0} because pattern matching does not continue after
the constraint guard \texttt{z =/= 0.0} fails. Instead, the whole case
expression fails in this case.

Our algorithm scans the arguments of the first alternative from left
to right until finding a literal or a constructor application. If such
a position is found, the alternatives are partitioned into groups such
that all alternatives in one group have a term with the same root or a
variable pattern at the selected position and the groups are defined
by mutually distinct roots. If no such position is found, the first
alternative is selected and the remaining alternatives are used in
order to define a default (case) expression when the selected
alternative is defined with a list of boolean guards.

Including alternatives with a variable pattern at the selected
position causes the aforementioned code duplication. The variable
patterns themselves are replaced by fresh instances of the pattern
defining the respective group. Note that the algorithm carefully
preserves the order of alternatives, which means that the first
alternatives of a group matching a literal or constructor rooted term
may have a variable pattern at the selected position.

Overloaded (numeric) literals complicate pattern matching because the
representation of an overloaded numeric literal is not known at
compile time. Therefore, case alternatives with an overloaded literal
pattern at the selected position are transformed into if-then-else
expressions using \verb|(==)| in order to check for matches. In
particular, an expression
\begin{quote}\tt
  case $x$ of \lb{} $i$ -> $e$; \emph{alts} \rb{}
\end{quote}
where $i$ is an overloaded numeric literal, is transformed into
\begin{quote}\tt
  if $x$ == $i$
  then case $x$ of \lb{} \emph{alts'} \rb{}
  else case $x$ of \lb{} \emph{alts''} \rb{}
\end{quote}
where $x$ is a fresh variable and \emph{alts'} and \emph{alts''} are
derived from \emph{alts} as follows
\begin{displaymath}
  \begin{array}{l@{}ll}
    \emph{alts'} &\null= \lbrace t_j' \rightarrow e_j \mid
      t_j \rightarrow e_j \in \emph{alts} \rbrace &
      t_j' = \left\lbrace \begin{array}{ll}
          x & \mbox{if $t_j = i$} \\
          t_j & \mbox{otherwise}
        \end{array} \right. \\
    \emph{alts''} &\null= \lbrace t_j \rightarrow e_j \mid
      t_j \rightarrow e_j \in \emph{alts}, t_j \not=i \rbrace
    \end{array}
\end{displaymath}
We use a case expression for the then branch in order to handle
guarded alternatives, which can fall through to the next alternatives,
and also case expressions where the literal occurs within another
pattern. Note that we keep all alternatives in \emph{alts'} because
different literals can have the same representation. This happens,
e.g., for a \texttt{Num Bool} instance with
\begin{verbatim}
  fromInteger n = odd n
\end{verbatim}

A further complication arises because numeric literals and constructor
rooted terms can occur at the same position in different alternatives
of a case expression. For instance, given type
\verb+data Nat = Z | S Nat+ and a suitable \verb|Num Nat| instance,
one could define (a rigid variant of) \verb|even| as follows.
\begin{verbatim}
  even n =
    case n of
      Z   -> True
      1   -> False
      S n -> not (even n)
\end{verbatim}
Since the compiler does not know the representation of literal
constants, it transforms such case expressions essentially into two
separate matches, one for the numeric literals and the other for the
constructor rooted terms. Thus, the above definition of \verb|even|
would be handled as if it were defined as follows.
\begin{verbatim}
  even n =
    case (n,n) of
      (_,Z)   -> True
      (1,_)   -> False
      (_,S n) -> not (even n)
\end{verbatim}

The algorithm also removes redundant default alternatives in case
expressions. As a simple example, consider the expression
\begin{verbatim}
  case x of
    Left y -> y
    Right z -> z
    _ -> undefined
\end{verbatim}
In this expression, the last alternative is never selected because the
first two alternatives already match all terms of type
\texttt{Either}. Since alternatives are partitioned according to the
roots of the terms at the selected position, we only need to compare
the number of groups of alternatives with the number of constructors
of the matched expression's type in order to check whether the default
pattern is redundant.

Note that the default case may no longer be redundant if there are
guarded alternatives, e.g.
\begin{verbatim}
  case x of
    Left y | y > 0 -> y
    Right z | z > 0 -> z
    _ -> 0
\end{verbatim}
Nevertheless, we do not need to treat such case expressions
differently with respect to the completeness test because the default
case is duplicated into the \texttt{Left} and \texttt{Right}
alternatives. Thus, the example is effectively transformed into
\begin{verbatim}
  case x of
    Left y -> if y > 0 then y else 0
    Right z -> if z > 0 then z else 0
    _ -> 0
\end{verbatim}
where the default alternative is redundant.
\begin{verbatim}

> asLiteral :: (a,Ident) -> ConstrTerm a -> ConstrTerm a
> asLiteral _ t@(LiteralPattern _ _) = t
> asLiteral v (VariablePattern _ _) = uncurry VariablePattern v
> asLiteral v (ConstructorPattern _ _ _) = uncurry VariablePattern v
> asLiteral v (AsPattern v' t) = AsPattern v' (asLiteral v t)

> asConstrApp :: (a,Ident) -> ConstrTerm a -> ConstrTerm a
> asConstrApp v (LiteralPattern _ _) = uncurry VariablePattern v
> asConstrApp _ t@(VariablePattern _ _) = t
> asConstrApp _ t@(ConstructorPattern _ _ _) = t
> asConstrApp v (AsPattern v' t) = AsPattern v' (asConstrApp v t)

> rigidMatch :: ModuleIdent -> Type -> ([(Type,Ident)] -> [(Type,Ident)])
>            -> [(Type,Ident)] -> [Match' Type]
>            -> CaseMatchState (Expression Type)
> rigidMatch _ ty _      _  []     = return (prelFailed ty)
> rigidMatch m ty prefix [] (a:as) =
>   rigidMatch m ty id vs (map resetArgs as) >>= toAlt vs a
>   where vs = prefix []
>         resetArgs (p,prefix,ts,rhs) = (p,id,prefix ts,rhs)
>         toAlt vs (p,prefix,_,rhs) =
>           matchRhs m p (foldr2 (bindVars p . snd) rhs vs (prefix []))
> rigidMatch m ty prefix (v:vs) as =
>   case fst (head as') of
>     VariablePattern _ _
>       | all (isVarPattern . fst) (tail as') ->
>           rigidMatch m ty prefix vs (map matchVar as)
>       | otherwise -> rigidMatch m ty (prefix . (v:)) vs (map skipArg as)
>     t'@(LiteralPattern _ l')
>       | fst v `elem` (charType:numTypes) ->
>           liftM (Case (uncurry mkVar v))
>                 (mapM (matchCaseAlt m ty prefix v vs as') (lts ++ vts))
>       | otherwise ->
>           liftM (Case (eqNum (fst v) v l'))
>                 (sequence [matchLitAlt True m ty prefix v vs as' t',
>                            matchLitAlt False m ty prefix v vs as' t'])
>     ConstructorPattern _ _ _
>       | null lts ->
>           do
>             tcEnv <- liftSt envRt
>             liftM (Case (uncurry mkVar v))
>                   (mapM (matchCaseAlt m ty prefix v vs as')
>                         (cts ++ if allCases tcEnv v cts then [] else vts))
>       | otherwise ->
>           rigidMatch m ty (prefix . (v:)) (v:vs) (map dupArg as)
>   where as' = map tagAlt as
>         (lts,cts,vts) = partitionPatterns (nub (map fst as'))
>         tagAlt (p,prefix,t:ts,rhs) = (pattern t,(p,prefix,t:ts,rhs))
>         skipArg (p,prefix,t:ts,rhs) = (p,prefix . (t:),ts,rhs)
>         matchVar (p,prefix,t:ts,rhs) = (p,prefix,ts,bindVars p (snd v) t rhs)
>         dupArg (p,prefix,t:ts,rhs) =
>           (p,prefix . (asLiteral v t :),asConstrApp v t:ts,rhs)
>         eqNum ty v l = apply (prelEq ty) [uncurry mkVar v,numLit ty l]
>         numLit ty (Integer i) =
>           Apply (prelFromInteger ty) (Literal integerType (Integer i))
>         numLit ty (Rational r) =
>           Apply (prelFromRational ty) (Literal rationalType (Rational r))
>         allCases tcEnv (ty,_) ts = length cs == length ts
>           where cs = constructors (rootOfType ty) tcEnv

> partitionPatterns :: [ConstrTerm a]
>                   -> ([ConstrTerm a],[ConstrTerm a],[ConstrTerm a])
> partitionPatterns = foldr partition ([],[],[])
>   where partition t@(LiteralPattern _ _) ~(lts,cts,vts) = (t:lts,cts,vts)
>         partition t@(VariablePattern _ _) ~(lts,cts,vts) = (lts,cts,t:vts)
>         partition t@(ConstructorPattern _ _ _) ~(lts,cts,vts) =
>           (lts,t:cts,vts)

> matchCaseAlt :: ModuleIdent -> Type -> ([(Type,Ident)] -> [(Type,Ident)])
>              -> (Type,Ident) -> [(Type,Ident)]
>              -> [(ConstrTerm (),Match' Type)] -> ConstrTerm ()
>              -> CaseMatchState (Alt Type)
> matchCaseAlt m ty prefix v vs as t =
>   do
>     vs' <- matchVars m (map arguments ts)
>     let ts' = map (uncurry VariablePattern) vs'
>     e' <- rigidMatch m ty id (prefix (vs' ++ vs)) (map (expandArg ts') as')
>     return (caseAlt (pos (head as')) (renameArgs (snd v) vs' t') e')
>   where t'
>           | isVarPattern t = uncurry VariablePattern v
>           | otherwise = head (filter (not . isVarPattern) ts)
>         ts = [t | (_,_,t:_,_) <- as']
>         as' = [a | (t',a) <- as, t' == t || isVarPattern t']
>         pos (p,_,_,_) = p
>         expandArg ts' (p,prefix,t:ts,rhs) =
>           (p,id,prefix (arguments' ts' t ++ ts),bindVars p (snd v) t rhs)
>         arguments' ts' t = if isVarPattern t then ts' else arguments t

> matchLitAlt :: Bool -> ModuleIdent -> Type
>             -> ([(Type,Ident)] -> [(Type,Ident)]) -> (Type,Ident)
>             -> [(Type,Ident)] -> [(ConstrTerm (),Match' Type)]
>             -> ConstrTerm () -> CaseMatchState (Alt Type)
> matchLitAlt eq m ty prefix v vs as t =
>   liftM (caseAlt (pos (head as')) t')
>         (rigidMatch m ty id (prefix (v:vs)) (map resetArgs as'))
>   where t' = if eq then truePattern else falsePattern
>         as'
>           | eq = [if t == t' then matchArg v a else a | (t',a) <- as]
>           | otherwise = [a | (t',a) <- as, t /= t']
>         pos (p,_,_,_) = p
>         matchArg v (p,prefix,t:ts,rhs) = (p,prefix,asConstrApp v t:ts,rhs)
>         resetArgs (p,prefix,ts,rhs) = (p,id,prefix ts,rhs)

\end{verbatim}
Generation of fresh names
\begin{verbatim}

> freshIdent :: ModuleIdent -> String -> Int -> TypeScheme
>            -> CaseMatchState Ident
> freshIdent m prefix n ty =
>   do
>     x <- liftM (mkName prefix) (liftSt (liftRt (updateSt (1 +))))
>     updateSt_ (bindFun m x n ty)
>     return x
>   where mkName pre n = mkIdent (pre ++ show n)

> freshVar :: Typeable a => ModuleIdent -> String -> a
>          -> CaseMatchState (Type,Ident)
> freshVar m prefix x =
>   do
>     v <- freshIdent m prefix 0 (monoType ty)
>     return (ty,v)
>   where ty = typeOf x

\end{verbatim}
Prelude entities
\begin{verbatim}

> prelEq, prelFromInteger, prelFromRational :: Type -> Expression Type
> prelEq ty = preludeFun [ty,ty] boolType "=="
> prelFromInteger ty = preludeFun [integerType] ty "fromInteger"
> prelFromRational ty = preludeFun [rationalType] ty "fromRational"

> prelFailed :: Type -> Expression Type
> prelFailed ty = preludeFun [] ty "failed"

> preludeFun :: [Type] -> Type -> String -> Expression Type
> preludeFun tys ty f =
>   Variable (foldr TypeArrow ty tys) (qualifyWith preludeMIdent (mkIdent f))

> truePattern, falsePattern, successPattern :: ConstrTerm Type
> truePattern = ConstructorPattern boolType qTrueId []
> falsePattern = ConstructorPattern boolType qFalseId []
> successPattern = ConstructorPattern successType qSuccessId []

\end{verbatim}
Auxiliary definitions
\begin{verbatim}

> mkRhs :: Position -> Expression a -> Rhs a
> mkRhs p e = SimpleRhs p e []

> mkCase :: ModuleIdent -> Position -> (a,Ident) -> Expression a -> Expression a
>        -> Expression a
> mkCase m _ (_,v) e (Case (Variable _ v') as)
>   | qualify v == v' && v `notElem` qfv m as = Case e as
> mkCase m _ (_,v) e (Fcase (Variable _ v') as)
>   | qualify v == v' && v `notElem` qfv m as = Fcase e as
> mkCase _ p (ty,v) e e' = Let [varDecl p ty v e] e'

> addDecl :: Decl a -> Rhs a -> Rhs a
> addDecl d (SimpleRhs p e ds) = SimpleRhs p e (d : ds)
> addDecl d (GuardedRhs es ds) = GuardedRhs es (d : ds)

> vars :: ConstrTerm Type -> [(Type,Ident)]
> vars (LiteralPattern _ _) = []
> vars (VariablePattern ty v) = [(ty,v) | unRenameIdent v /= anonId]
> vars (ConstructorPattern _ _ ts) = concatMap vars ts
> vars (AsPattern v t) = (typeOf t,v) : vars t

> tuplePattern :: [(Type,Ident)] -> ConstrTerm Type
> tuplePattern vs =
>   case vs of
>     [] -> ConstructorPattern unitType qUnitId []
>     [v] -> uncurry VariablePattern v
>     _ -> TuplePattern (map (uncurry VariablePattern) vs)

> tupleExpr :: [(Type,Ident)] -> Expression Type
> tupleExpr vs =
>   case vs of
>     [] -> Constructor unitType qUnitId
>     [v] -> uncurry mkVar v
>     _ -> Tuple (map (uncurry mkVar) vs)

\end{verbatim}
