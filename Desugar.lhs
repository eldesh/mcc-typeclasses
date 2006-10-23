% -*- LaTeX -*-
% $Id: Desugar.lhs 1979 2006-10-23 19:05:25Z wlux $
%
% Copyright (c) 2001-2006, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Desugar.lhs}
\section{Desugaring Curry Expressions}
The desugaring pass removes all syntactic sugar from the module. In
particular, the output of the desugarer will have the following
properties.
\begin{itemize}
\item All function definitions are $\eta$-expanded.
\item No guarded right hand sides occur in equations, pattern
  declarations, and case alternatives. In addition, the declaration
  lists of the right hand sides are empty; local declarations are
  transformed into let expressions.
\item Patterns in equations and case alternatives are composed only of
  \begin{itemize}
  \item literals,
  \item variables,
  \item constructor applications, and
  \item as patterns.
  \end{itemize}
\item Expressions are composed only of
  \begin{itemize}
  \item literals,
  \item variables,
  \item constructors,
  \item (binary) applications,
  \item let expressions, and
  \item case expressions.
  \end{itemize}
\item Patterns in case expression are restricted further in that all
  arguments of a constructor pattern are variable patterns.
\item Applications $N\:x$ in patterns and expressions, where $N$ is a
  newtype constructor, are replaced by a $x$. Note that neither the
  newtype declaration itself nor partial applications of newtype
  constructors are changed.\footnote{It were possible to replace
  partial applications of newtype constructor by \texttt{Prelude.id}.
  However, our solution yields a more accurate output when the result
  of a computation includes partial applications.}
\end{itemize}

\ToDo{Use a different representation for the restricted code instead
of using the syntax tree from \texttt{CurrySyntax}.}

\textbf{As we are going to insert references to real prelude entities,
all names must be properly qualified before calling this module.}
\begin{verbatim}

> module Desugar(desugar,desugarGoal) where
> import Base
> import Combined
> import List
> import Monad
> import TopEnv
> import Typing
> import Utils

\end{verbatim}
New identifiers may be introduced while desugaring pattern
declarations, case and $\lambda$-expressions, and list comprehensions.
As usual, we use a state monad transformer for generating unique
names. In addition, the state is also used for passing through the
type environment, which must be augmented with the types of these new
variables.
\begin{verbatim}

> type DesugarState a = StateT ValueEnv (ReaderT TCEnv (StateT Int Id)) a

> run :: DesugarState a -> TCEnv -> ValueEnv -> a
> run m tcEnv tyEnv = runSt (callRt (callSt m tyEnv) tcEnv) 1

\end{verbatim}
During desugaring, the compiler transforms constraint guards into case
expressions matching the guards against the constructor
\texttt{Success}, which is defined in the runtime system. Thus, the
compiler assumes that the type \texttt{Success} is defined by
\begin{verbatim}
  data Success = Success
\end{verbatim}
Since the internal constructor \texttt{Success} occurs in the
desugared code, its type is added to the type environment.

Note that the definition of \texttt{Success} is not included in the
prelude because the \texttt{Success} constructor would not be
accessible in any module other than the prelude unless the constructor
were also exported from the prelude. However, that would be
incompatible with the Curry report, which deliberately defines
\texttt{Success} as an abstract type.
\begin{verbatim}

> bindSuccess :: ValueEnv -> ValueEnv
> bindSuccess = localBindTopEnv successId successCon
>   where successCon =
>           DataConstructor (qualify successId) (polyType successType)

\end{verbatim}
The desugaring phase keeps only the type, function, and value
declarations of the module. As type declarations are not desugared and
cannot occur in local declaration groups they are filtered out
separately.

Actually, the transformation is slightly more general than necessary,
as it allows pattern and free variable declarations at the top-level
of a module.
\begin{verbatim}

> desugar :: TCEnv -> ValueEnv -> Module -> (Module,ValueEnv)
> desugar tcEnv tyEnv (Module m es is ds) = (Module m es is ds',tyEnv')
>   where (ds',tyEnv') = run (desugarModule m ds) tcEnv (bindSuccess tyEnv)

> desugarModule :: ModuleIdent -> [TopDecl] -> DesugarState ([TopDecl],ValueEnv)
> desugarModule m ds =
>   do
>     vds' <- desugarDeclGroup m [d | BlockDecl d <- vds]
>     tyEnv' <- fetchSt
>     return (tds ++ map BlockDecl vds',tyEnv')
>   where (tds,vds) = partition isTypeDecl ds

\end{verbatim}
While a goal of type \texttt{IO \_} is executed directly by the
runtime system, all other goals are evaluated under an interactive
top-level which displays the solutions of the goal and in particular
the bindings of the free variables. For this reason, the free
variables declared in the \texttt{where} clause of a goal are
translated into free variables of the goal. In addition, the goal
is transformed into a first order expression by performing a
unification with another variable. Thus, a goal
\begin{quote}
 \emph{expr}
 \texttt{where} $v_1$,\dots,$v_n$ \texttt{free}; \emph{decls}
\end{quote}
where no free variable declarations occur in \emph{decls} is
translated into the function
\begin{quote}
  \emph{f} $v_0$ $v_1$ \dots{} $v_n$ \texttt{=}
    $v_0$ \texttt{=:=} \emph{expr}
    \texttt{where} \emph{decls}
\end{quote}
where $v_0$ is a fresh variable.

\textbf{Note:} The debugger assumes that the goal is always a nullary
function. This means that we must not $\eta$-expand functional goal
expressions. In order to avoid the $\eta$-expansion we cheat a little
bit here and change the type of the goal into $\forall\alpha.\alpha$
if it really has a functional type.

\ToDo{Fix the debugger to handle functional goals so that this
hack is no longer needed.}
\begin{verbatim}

> desugarGoal :: Bool -> TCEnv -> ValueEnv -> ModuleIdent -> Ident -> Goal
>             -> (Maybe [Ident],Module,ValueEnv)
> desugarGoal debug tcEnv tyEnv m g (Goal p e ds)
>   | debug || isIO ty =
>       desugarGoalIO tcEnv (bindSuccess tyEnv) p m g (Let ds e)
>         (if debug && arrowArity ty > 0 then typeVar 0 else ty)
>   | otherwise = desugarGoal' tcEnv (bindSuccess tyEnv) p m g vs e' ty
>   where ty = typeOf tyEnv e
>         (vs,e') = liftGoalVars (if null ds then e else Let ds e)
>         isIO (TypeConstructor tc [_]) = tc == qIOId
>         isIO _ = False

> desugarGoalIO :: TCEnv -> ValueEnv -> Position -> ModuleIdent
>               -> Ident -> Expression -> Type
>               -> (Maybe [Ident],Module,ValueEnv)
> desugarGoalIO tcEnv tyEnv p m g e ty =
>   (Nothing,
>    Module m Nothing [] [goalDecl p g [] e'],
>    bindFun m g (polyType ty) tyEnv')
>   where (e',tyEnv') = run (desugarGoalExpr m e) tcEnv tyEnv

> desugarGoal' :: TCEnv -> ValueEnv -> Position -> ModuleIdent
>              -> Ident -> [Ident] -> Expression -> Type
>              -> (Maybe [Ident],Module,ValueEnv)
> desugarGoal' tcEnv tyEnv p m g vs e ty =
>   (Just vs',
>    Module m Nothing [] [goalDecl p g (v0:vs') (apply prelUnif [mkVar v0,e'])],
>    bindFun m v0 (monoType ty) (bindFun m g (polyType ty') tyEnv'))
>   where (e',tyEnv') = run (desugarGoalExpr m e) tcEnv tyEnv
>         v0 = anonId
>         vs' = filter (`elem` qfv m e') vs
>         ty' = TypeArrow ty (foldr (TypeArrow . typeOf tyEnv) successType vs')

> goalDecl :: Position -> Ident -> [Ident] -> Expression -> TopDecl
> goalDecl p g vs e = BlockDecl (funDecl p g (map VariablePattern vs) e)

> desugarGoalExpr :: ModuleIdent -> Expression
>                 -> DesugarState (Expression,ValueEnv)
> desugarGoalExpr m e =
>   do
>     e' <- desugarExpr m (first "") e
>     tyEnv' <- fetchSt
>     return (e',tyEnv')

> liftGoalVars :: Expression -> ([Ident],Expression)
> liftGoalVars (Let ds e) = (concat [vs | FreeDecl _ vs <- vds],Let ds' e)
>   where (vds,ds') = partition isFreeDecl ds
> liftGoalVars e = ([],e)

\end{verbatim}
Within a declaration group, all fixity declarations, type signatures
and trust annotations are discarded. First, the patterns occurring in
the left hand sides are desugared. Due to lazy patterns this may add
further declarations to the group that must be desugared as well.
\begin{verbatim}

> desugarDeclGroup :: ModuleIdent -> [Decl] -> DesugarState [Decl]
> desugarDeclGroup m ds =
>   do
>     dss' <- mapM (desugarDeclLhs m) (filter isValueDecl ds)
>     mapM (desugarDeclRhs m) (concat dss')

> desugarDeclLhs :: ModuleIdent -> Decl -> DesugarState [Decl]
> desugarDeclLhs m (PatternDecl p t rhs) =
>   do
>     (ds',t') <- desugarTerm m p [] t
>     dss' <- mapM (desugarDeclLhs m) ds'
>     return (PatternDecl p t' rhs : concat dss')
> desugarDeclLhs _ d = return [d]

\end{verbatim}
After desugaring its right hand side, each equation is $\eta$-expanded
by adding as many variables as necessary to the argument list and
applying the right hand side to those variables. The import entity
specification of foreign functions using the \texttt{ccall} calling
convention is expanded to always include the kind of the declaration
(either \texttt{static} or \texttt{dynamic}) and the name of the
imported function.
\begin{verbatim}

> desugarDeclRhs :: ModuleIdent -> Decl -> DesugarState Decl
> desugarDeclRhs m (FunctionDecl p f eqs) =
>   do
>     ty <- liftM (flip typeOf f) fetchSt
>     liftM (FunctionDecl p f) (mapM (desugarEquation m (arrowArgs ty)) eqs)
> desugarDeclRhs _ (ForeignDecl p cc ie f ty) =
>   return (ForeignDecl p cc (desugarImpEnt cc ie) f ty)
>   where desugarImpEnt CallConvPrimitive ie = ie `mplus` Just (name f)
>         desugarImpEnt CallConvCCall ie =
>           Just (unwords (kind (maybe [] words ie)))
>         kind [] = "static" : ident []
>         kind (x:xs)
>           | x == "static" = x : ident xs
>           | x == "dynamic" = [x]
>           | otherwise = "static" : ident (x:xs)
>         ident [] = [name f]
>         ident [x]
>           | x == "&" || ".h" `isSuffixOf` x = [x,name f]
>           | otherwise = [x]
>         ident [h,x]
>           | x == "&" = [h,x,name f]
>           | otherwise = [h,x]
>         ident [h,amp,f] = [h,amp,f]
>         ident _ = internalError "desugarImpEnt CallConvCCall"
> desugarDeclRhs m (PatternDecl p t rhs) =
>   liftM (PatternDecl p t) (desugarRhs m p rhs)
> desugarDeclRhs _ (FreeDecl p vs) = return (FreeDecl p vs)

> desugarEquation :: ModuleIdent -> [Type] -> Equation -> DesugarState Equation
> desugarEquation m tys (Equation p lhs rhs) =
>   do
>     vs <- mapM (freshIdent m "_#eta" . monoType) (drop (length ts) tys)
>     (ds',ts') <- mapAccumM (desugarTerm m p) [] ts
>     rhs' <- desugarRhs m p (addDecls ds' rhs)
>     return (Equation p (FunLhs f (ts' ++ map VariablePattern vs))
>                      (applyRhs rhs' (map mkVar vs)))
>   where (f,ts) = flatLhs lhs
>         applyRhs (SimpleRhs p e _) vs = SimpleRhs p (apply e vs) []

\end{verbatim}
The transformation of patterns is straight forward except for lazy
patterns. A lazy pattern \texttt{\~}$t$ is replaced by a fresh
variable $v$ and a new local declaration $t$~\texttt{=}~$v$ in the
scope of the pattern. In addition, as-patterns $v$\texttt{@}$t$ where
$t$ is a variable or an as-pattern are replaced by $t$ in combination
with a local declaration for $v$.
\begin{verbatim}

> desugarLiteral :: Literal -> Either Literal [Literal]
> desugarLiteral (Char c) = Left (Char c)
> desugarLiteral (Int i) = Left (Int i)
> desugarLiteral (Float f) = Left (Float f)
> desugarLiteral (String cs) = Right (map Char cs)

> desugarTerm :: ModuleIdent -> Position -> [Decl] -> ConstrTerm
>             -> DesugarState ([Decl],ConstrTerm)
> desugarTerm m p ds (LiteralPattern l) =
>   either (return . (,) ds . LiteralPattern)
>          (desugarTerm m p ds . ListPattern . map LiteralPattern)
>          (desugarLiteral l)
> desugarTerm m p ds (NegativePattern _ l) =
>   desugarTerm m p ds (LiteralPattern (negateLiteral l))
>   where negateLiteral (Int i) = Int (-i)
>         negateLiteral (Float f) = Float (-f)
>         negateLiteral _ = internalError "negateLiteral"
> desugarTerm _ _ ds (VariablePattern v) = return (ds,VariablePattern v)
> desugarTerm m p ds (ConstructorPattern c [t]) =
>   do
>     tyEnv <- fetchSt
>     liftM (if isNewtypeConstr tyEnv c then id else apSnd (constrPat c))
>           (desugarTerm m p ds t)
>   where constrPat c t = ConstructorPattern c [t]
> desugarTerm m p ds (ConstructorPattern c ts) =
>   liftM (apSnd (ConstructorPattern c)) (mapAccumM (desugarTerm m p) ds ts)
> desugarTerm m p ds (InfixPattern t1 op t2) =
>   desugarTerm m p ds (ConstructorPattern op [t1,t2])
> desugarTerm m p ds (ParenPattern t) = desugarTerm m p ds t
> desugarTerm m p ds (TuplePattern ts) =
>   desugarTerm m p ds (ConstructorPattern (qTupleId (length ts)) ts)
> desugarTerm m p ds (ListPattern ts) =
>   liftM (apSnd (foldr cons nil)) (mapAccumM (desugarTerm m p) ds ts)
>   where nil = ConstructorPattern qNilId []
>         cons t ts = ConstructorPattern qConsId [t,ts]
> desugarTerm m p ds (AsPattern v t) =
>   liftM (desugarAs p v) (desugarTerm m p ds t)
> desugarTerm m p ds (LazyPattern t) = desugarLazy m p ds t

> desugarAs :: Position -> Ident -> ([Decl],ConstrTerm) -> ([Decl],ConstrTerm)
> desugarAs p v (ds,t) =
>  case t of
>    VariablePattern v' -> (varDecl p v (mkVar v') : ds,t)
>    AsPattern v' _ -> (varDecl p v (mkVar v') : ds,t)
>    _ -> (ds,AsPattern v t)

> desugarLazy :: ModuleIdent -> Position -> [Decl] -> ConstrTerm
>             -> DesugarState ([Decl],ConstrTerm)
> desugarLazy m p ds t =
>   case t of
>     VariablePattern _ -> return (ds,t)
>     ParenPattern t' -> desugarLazy m p ds t'
>     AsPattern v t' -> liftM (desugarAs p v) (desugarLazy m p ds t')
>     LazyPattern t' -> desugarLazy m p ds t'
>     _ ->
>       do
>         v' <- freshVar m "_#lazy" t
>         return (patDecl p t (mkVar v') : ds,VariablePattern v')

\end{verbatim}
A list of boolean guards is expanded into a nested if-then-else
expression, whereas a constraint guard is replaced by a case
expression. Note that if the guard type is \texttt{Success} only a
single guard is allowed for each equation.\footnote{This change was
introduced in version 0.8 of the Curry report.} We check for the
type \texttt{Bool} of the guard because the guard's type defaults to
\texttt{Success} if it is not restricted by the guard expression.
\begin{verbatim}

> desugarRhs :: ModuleIdent -> Position -> Rhs -> DesugarState Rhs
> desugarRhs m p rhs =
>   do
>     tyEnv <- fetchSt
>     e' <- desugarExpr m p (expandRhs tyEnv prelFailed rhs)
>     return (SimpleRhs p e' [])

> expandRhs :: ValueEnv -> Expression -> Rhs -> Expression
> expandRhs tyEnv _ (SimpleRhs _ e ds) = Let ds e
> expandRhs tyEnv e0 (GuardedRhs es ds) = Let ds (expandGuards tyEnv e0 es)

> expandGuards :: ValueEnv -> Expression -> [CondExpr] -> Expression
> expandGuards tyEnv e0 es
>   | booleanGuards tyEnv es = foldr mkIfThenElse e0 es
>   | otherwise = mkCase es
>   where mkIfThenElse (CondExpr _ g e) = IfThenElse g e
>         mkCase [CondExpr p g e] = Case g [caseAlt p successPattern e]

> booleanGuards :: ValueEnv -> [CondExpr] -> Bool
> booleanGuards _ [] = False
> booleanGuards tyEnv (CondExpr _ g _ : es) =
>   not (null es) || typeOf tyEnv g == boolType

> desugarExpr :: ModuleIdent -> Position -> Expression
>             -> DesugarState Expression
> desugarExpr m p (Literal l) =
>   either (return . Literal) (desugarExpr m p . List . map Literal)
>          (desugarLiteral l)
> desugarExpr _ _ (Variable v) = return (Variable v)
> desugarExpr _ _ (Constructor c) = return (Constructor c)
> desugarExpr m p (Paren e) = desugarExpr m p e
> desugarExpr m p (Typed e _) = desugarExpr m p e
> desugarExpr m p (Tuple es) =
>   liftM (apply (Constructor (qTupleId (length es))))
>         (mapM (desugarExpr m p) es)
> desugarExpr m p (List es) = liftM (foldr cons nil) (mapM (desugarExpr m p) es)
>   where nil = Constructor qNilId
>         cons = Apply . Apply (Constructor qConsId)
> desugarExpr m p (ListCompr e []) = desugarExpr m p (List [e])
> desugarExpr m p (ListCompr e (q:qs)) = desugarQual m p q (ListCompr e qs)
> desugarExpr m p (EnumFrom e) = liftM (Apply prelEnumFrom) (desugarExpr m p e)
> desugarExpr m p (EnumFromThen e1 e2) =
>   liftM (apply prelEnumFromThen) (mapM (desugarExpr m p) [e1,e2])
> desugarExpr m p (EnumFromTo e1 e2) =
>   liftM (apply prelEnumFromTo) (mapM (desugarExpr m p) [e1,e2])
> desugarExpr m p (EnumFromThenTo e1 e2 e3) =
>   liftM (apply prelEnumFromThenTo) (mapM (desugarExpr m p) [e1,e2,e3])
> desugarExpr m p (UnaryMinus op e) =
>   do
>     tyEnv <- fetchSt
>     liftM (Apply (unaryMinus op (typeOf tyEnv e))) (desugarExpr m p e)
>   where unaryMinus op ty
>           | op == minusId =
>               if ty == floatType then prelNegateFloat else prelNegate
>           | op == fminusId = prelNegateFloat
>           | otherwise = internalError "unaryMinus"
> desugarExpr m p (Apply (Constructor c) e) =
>   do
>     tyEnv <- fetchSt
>     liftM (if isNewtypeConstr tyEnv c then id else (Apply (Constructor c)))
>           (desugarExpr m p e)
> desugarExpr m p (Apply e1 e2) =
>   do
>     e1' <- desugarExpr m p e1
>     e2' <- desugarExpr m p e2
>     return (Apply e1' e2')
> desugarExpr m p (InfixApply e1 op e2) =
>   do
>     op' <- desugarExpr m p (infixOp op)
>     e1' <- desugarExpr m p e1
>     e2' <- desugarExpr m p e2
>     return (Apply (Apply op' e1') e2')
> desugarExpr m p (LeftSection e op) =
>   do
>     op' <- desugarExpr m p (infixOp op)
>     e' <- desugarExpr m p e
>     return (Apply op' e')
> desugarExpr m p (RightSection op e) =
>   do
>     op' <- desugarExpr m p (infixOp op)
>     e' <- desugarExpr m p e
>     return (Apply (Apply prelFlip op') e')
> desugarExpr m p (Lambda ts e) =
>   do
>     f <- freshFun m "_#lambda" (Lambda ts e)
>     desugarExpr m p (Let [funDecl p f ts e] (mkVar f))
> desugarExpr m p (Let ds e) =
>   do
>     ds' <- desugarDeclGroup m ds
>     e' <- desugarExpr m p e
>     return (if null ds' then e' else Let ds' e')
> desugarExpr m p (Do sts e) = desugarExpr m p (foldr desugarStmt e sts)
>   where desugarStmt (StmtExpr e) e' = apply prelBind_ [e,e']
>         desugarStmt (StmtBind t e) e' = apply prelBind [e,Lambda [t] e']
>         desugarStmt (StmtDecl ds) e' = Let ds e'
> desugarExpr m p (IfThenElse e1 e2 e3) =
>   do
>     e1' <- desugarExpr m p e1
>     e2' <- desugarExpr m p e2
>     e3' <- desugarExpr m p e3
>     return (Case e1' [caseAlt p truePattern e2',caseAlt p falsePattern e3'])
> desugarExpr m p (Case e alts) =
>   do
>     v <- freshVar m "_#case" (head ts)
>     e' <- desugarExpr m p e
>     liftM (mkCase m v e') 
>           (mapM (liftM fromAlt . desugarAltLhs m) alts >>=
>            desugarCase m id [v])
>   where ts = [t | Alt p t rhs <- alts]
>         fromAlt (Alt p t rhs) = (p,id,[t],rhs)
>         mkCase m v e (Case e' alts)
>           | mkVar v == e' && v `notElem` qfv m alts = Case e alts
>         mkCase _ v e e' = Let [varDecl p v e] e'

\end{verbatim}
Case expressions with nested patterns are transformed into nested case
expressions where each expression uses only flat patterns. The
algorithm used here is a variant of the algorithm used for
transforming pattern matching of function heads into case expressions
(see Sect.~\ref{sec:il-trans}). In contrast to the algorithm presented
in Sect.~5 of~\cite{PeytonJones87:Book}, the code generated by our
algorithm will not perform redundant matches. Furthermore, we do not
need a special pattern match failure primitive and fatbar expressions
in order to catch such failures. On the other hand, our algorithm can
cause code duplication. We do not care about that because most pattern
matching in Curry programs occurs in function heads and not in case
expressions.

The essential difference between pattern matching in case expressions
and function heads is that in case expressions, alternatives are
matched from top to bottom and evaluation commits to the first
alternative with a matching pattern. As an extension, we support
constraint and boolean guards in case expressions. If all boolean
guards of an alternative fail, pattern matching continues with the
next alternative as if the pattern did not match. No such fall-through
behavior applies to constraint guards since it cannot be implemented
without negation of constraints. For instance, the expression
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
that all alternatives in one group have a term with the same root at
the selected position and all groups are defined by mutually distinct
roots. Furthermore, alternatives with a variable pattern at the
selected position are included in all groups, which causes the
aforementioned code duplication, and the variables are replaced by a
fresh instance of the pattern defining the group. If no such position
is found, the first alternative is selected and the remaining
alternatives are used in order to define a default (case) expression
when the selected alternative is defined with a list of boolean
guards.

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
pattern is redundant. This works also for characters and numbers, as
there are no constructors associated with the corresponding types and,
therefore, default alternatives are never considered redundant when
matching against literals.

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

> type Match = (Position,[ConstrTerm] -> [ConstrTerm],[ConstrTerm],Rhs)

> pattern :: Ident -> ConstrTerm -> ConstrTerm
> pattern v (LiteralPattern l) = AsPattern v (LiteralPattern l)
> pattern v (VariablePattern _) = VariablePattern v
> pattern v (ConstructorPattern c ts) = AsPattern v (ConstructorPattern c ts')
>   where ts' = zipWith (const . VariablePattern) (repeat anonId) ts
> pattern v (AsPattern _ t) = pattern v t

> arguments :: ConstrTerm -> [ConstrTerm]
> arguments (LiteralPattern _) = []
> arguments (VariablePattern _) = []
> arguments (ConstructorPattern _ ts) = ts
> arguments (AsPattern _ t) = arguments t

> bindVars :: Position -> Ident -> ConstrTerm -> Rhs -> Rhs
> bindVars _ _ (LiteralPattern _) = id
> bindVars p v (VariablePattern v')
>   | v /= v' = addDecls [varDecl p v' (mkVar v)]
>   | otherwise = id
> bindVars _ _ (ConstructorPattern _ _) = id
> bindVars p v (AsPattern v' t) =
>   addDecls [varDecl p v' (mkVar v)] . bindVars p v t

> desugarAltLhs :: ModuleIdent -> Alt -> DesugarState Alt
> desugarAltLhs m (Alt p t rhs) =
>   do
>     (ds',t') <- desugarTerm m p [] t
>     return (Alt p t' (addDecls ds' rhs))

> desugarAltRhs :: ModuleIdent -> Alt -> Expression -> DesugarState Expression
> desugarAltRhs m (Alt p _ rhs) e0 =
>   do
>     tyEnv <- fetchSt
>     desugarExpr m p (expandRhs tyEnv e0 rhs)

> desugarCase :: ModuleIdent -> ([Ident] -> [Ident]) -> [Ident] -> [Match]
>             -> DesugarState Expression
> desugarCase _ _ _ [] = return prelFailed
> desugarCase m prefix [] (alt : alts) =
>   desugarCase m id vs (map resetArgs alts) >>=
>   desugarAltRhs m (toAlt vs alt)
>   where vs = prefix []
>         resetArgs (p,prefix,ts,rhs) = (p,id,prefix ts,rhs)
>         toAlt vs (p,prefix,_,rhs) =
>           Alt p (VariablePattern anonId)
>               (foldr2 (bindVars p) rhs vs (prefix []))
> desugarCase m prefix (v:vs) alts
>   | isVarPattern (fst (head alts')) =
>       if all isVarPattern (map fst (tail alts')) then
>         desugarCase m prefix vs (map dropArg alts)
>       else
>         desugarCase m (prefix . (v:)) vs (map skipArg alts)
>   | otherwise =
>       do
>         tcEnv <- liftSt envRt
>         tyEnv <- fetchSt
>         liftM (Case (mkVar v))
>               (mapM (desugarAlt m prefix vs alts')
>                     (if allCases tcEnv tyEnv v ts then ts else ts ++ ts'))
>   where alts' = map tagAlt alts
>         (ts',ts) = partition isVarPattern (nub (map fst alts'))
>         tagAlt (p,prefix,t:ts,rhs) =
>           (pattern v t,(p,prefix,t:ts,bindVars p v t rhs))
>         skipArg (p,prefix,t:ts,rhs) = (p,prefix . (t:),ts,rhs)
>         dropArg (p,prefix,t:ts,rhs) = (p,prefix,ts,bindVars p v t rhs)
>         allCases tcEnv tyEnv v ts = length cs == length ts
>           where TypeConstructor tc _ = fixType (typeOf tyEnv v)
>                 cs = constructors tc tcEnv
>         fixType (TypeConstrained (ty:_) _) = ty
>         fixType ty = ty

> desugarAlt :: ModuleIdent -> ([Ident] -> [Ident]) -> [Ident]
>            -> [(ConstrTerm,Match)] -> ConstrTerm -> DesugarState Alt
> desugarAlt m prefix vs alts t =
>   do
>     vs' <- mapM (freshVar m "_#case") (arguments t')
>     liftM (caseAlt (pos (snd (head alts'))) (renameArgs vs' t))
>           (desugarCase m id (prefix (vs' ++ vs))
>                        (map (expandArgs vs' . snd) alts'))
>   where alts' = filter (matchedBy t . fst) alts
>         t' = matchedArg (snd (head (filter ((t ==) . fst) alts')))
>         t1 `matchedBy` t2 = t1 == t2 || isVarPattern t2
>         pos (p,_,_,_) = p
>         matchedArg (_,_,t:_,_) = t
>         expandArgs vs (p,prefix,t:ts,rhs) =
>           (p,id,prefix (expandPatternArgs vs t ++ ts),rhs)
>         expandPatternArgs vs t
>           | isVarPattern t = map VariablePattern vs
>           | otherwise = arguments t

> renameArgs :: [Ident] -> ConstrTerm -> ConstrTerm
> renameArgs _ (LiteralPattern l) = LiteralPattern l
> renameArgs _ (VariablePattern v) = VariablePattern v
> renameArgs vs (ConstructorPattern c _) =
>   ConstructorPattern c (map VariablePattern vs)
> renameArgs vs (AsPattern v t) = AsPattern v (renameArgs vs t)

\end{verbatim}
In general, a list comprehension of the form
\texttt{[}$e$~\texttt{|}~$t$~\texttt{<-}~$l$\texttt{,}~\emph{qs}\texttt{]}
is transformed into an expression \texttt{foldr}~$f$~\texttt{[]}~$l$ where $f$
is a new function defined as
\begin{quote}
  \begin{tabbing}
    $f$ $x$ \emph{xs} \texttt{=} \\
    \quad \= \texttt{case} $x$ \texttt{of} \\
          \> \quad \= $t$ \texttt{->} \texttt{[}$e$ \texttt{|} \emph{qs}\texttt{]} \texttt{++} \emph{xs} \\
          \>       \> \texttt{\_} \texttt{->} \emph{xs}
  \end{tabbing}
\end{quote}
Note that this translation evaluates the elements of $l$ rigidly,
whereas the translation given in the Curry report is flexible.
However, it does not seem very useful to have the comprehension
generate instances of $t$ which do not contribute to the list.

Actually, we generate slightly better code in a few special cases.
When $t$ is a plain variable, the \texttt{case} expression degenerates
into a let-binding and the auxiliary function thus becomes an alias
for \texttt{(++)}. Instead of \texttt{foldr~(++)} we use the
equivalent prelude function \texttt{concatMap}. In addition, if the
remaining list comprehension in the body of the auxiliary function has
no qualifiers -- i.e., if it is equivalent to \texttt{[$e$]} -- we
avoid the construction of the singleton list by calling \texttt{(:)}
instead of \texttt{(++)} and \texttt{map} in place of
\texttt{concatMap}, respectively.
\begin{verbatim}

> desugarQual :: ModuleIdent -> Position -> Statement -> Expression
>             -> DesugarState Expression
> desugarQual m p (StmtExpr b) e = desugarExpr m p (IfThenElse b e (List []))
> desugarQual m p (StmtBind t l) e
>   | isVarPattern t = desugarExpr m p (qualExpr t e l)
>   | otherwise =
>       do
>         tyEnv <- fetchSt
>         v <- freshVar m "_#var" t
>         l' <- freshVar m "_#var" e
>         desugarExpr m p (apply prelFoldr [foldFunct v l' e,List [],l])
>   where qualExpr v (ListCompr e []) l = apply prelMap [Lambda [v] e,l]
>         qualExpr v e l = apply prelConcatMap [Lambda [v] e,l]
>         foldFunct v l e =
>           Lambda (map VariablePattern [v,l])
>             (Case (mkVar v)
>                   [caseAlt p t (append e (mkVar l)),
>                    caseAlt p (VariablePattern v) (mkVar l)])
>         append (ListCompr e []) l = apply (Constructor qConsId) [e,l]
>         append e l = apply prelAppend [e,l]
> desugarQual m p (StmtDecl ds) e = desugarExpr m p (Let ds e)

\end{verbatim}
Generation of fresh names
\begin{verbatim}

> freshIdent :: ModuleIdent -> String -> TypeScheme -> DesugarState Ident
> freshIdent m prefix ty =
>   do
>     x <- liftM (mkName prefix) (liftSt (liftRt (updateSt (1 +))))
>     updateSt_ (bindFun m x ty)
>     return x
>   where mkName pre n = mkIdent (pre ++ show n)

> freshVar :: Typeable a => ModuleIdent -> String -> a -> DesugarState Ident
> freshVar m prefix x =
>   do
>     tyEnv <- fetchSt
>     freshIdent m prefix (monoType (typeOf tyEnv x))

> freshFun :: Typeable a => ModuleIdent -> String -> a -> DesugarState Ident
> freshFun m prefix x =
>   do
>     tyEnv <- fetchSt
>     freshIdent m prefix (polyType (typeOf tyEnv x))

\end{verbatim}
Prelude entities
\begin{verbatim}

> prelUnif = Variable $ preludeIdent "=:="
> prelBind = Variable $ preludeIdent ">>="
> prelBind_ = Variable $ preludeIdent ">>"
> prelFlip = Variable $ preludeIdent "flip"
> prelEnumFrom = Variable $ preludeIdent "enumFrom"
> prelEnumFromTo = Variable $ preludeIdent "enumFromTo"
> prelEnumFromThen = Variable $ preludeIdent "enumFromThen"
> prelEnumFromThenTo = Variable $ preludeIdent "enumFromThenTo"
> prelFailed = Variable $ preludeIdent "failed"
> prelMap = Variable $ preludeIdent "map"
> prelFoldr = Variable $ preludeIdent "foldr"
> prelAppend = Variable $ preludeIdent "++"
> prelConcatMap = Variable $ preludeIdent "concatMap"
> prelNegate = Variable $ preludeIdent "negate"
> prelNegateFloat = Variable $ preludeIdent "negateFloat"

> truePattern = ConstructorPattern qTrueId []
> falsePattern = ConstructorPattern qFalseId []
> successPattern = ConstructorPattern (qualify successId) []

> preludeIdent :: String -> QualIdent
> preludeIdent = qualifyWith preludeMIdent . mkIdent

\end{verbatim}
Auxiliary definitions
\begin{verbatim}

> isVarPattern :: ConstrTerm -> Bool
> isVarPattern (VariablePattern _) = True
> isVarPattern (ParenPattern t) = isVarPattern t
> isVarPattern (AsPattern _ t) = isVarPattern t
> isVarPattern (LazyPattern _) = True
> isVarPattern _ = False

> funDecl :: Position -> Ident -> [ConstrTerm] -> Expression -> Decl
> funDecl p f ts e =
>   FunctionDecl p f [Equation p (FunLhs f ts) (SimpleRhs p e [])]

> patDecl :: Position -> ConstrTerm -> Expression -> Decl
> patDecl p t e = PatternDecl p t (SimpleRhs p e [])

> varDecl :: Position -> Ident -> Expression -> Decl
> varDecl p = patDecl p . VariablePattern

> addDecls :: [Decl] -> Rhs -> Rhs
> addDecls ds (SimpleRhs p e ds') = SimpleRhs p e (ds ++ ds')
> addDecls ds (GuardedRhs es ds') = GuardedRhs es (ds ++ ds')

> caseAlt :: Position -> ConstrTerm -> Expression -> Alt
> caseAlt p t e = Alt p t (SimpleRhs p e [])

> apply :: Expression -> [Expression] -> Expression
> apply = foldl Apply

> mkVar :: Ident -> Expression
> mkVar = Variable . qualify

\end{verbatim}
