% -*- LaTeX -*-
% $Id: Desugar.lhs 2738 2008-07-16 14:47:52Z wlux $
%
% Copyright (c) 2001-2008, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Desugar.lhs}
\section{Desugaring Curry Expressions}\label{sec:desugar}
The desugaring pass removes all syntactic sugar from the module. In
particular, the output of the desugarer will have the following
properties.
\begin{itemize}
\item No guarded right hand sides occur in equations, pattern
  declarations, and (f)case alternatives. In addition, the declaration
  lists of the right hand sides are empty; local declarations are
  transformed into let expressions.
\item Patterns in equations and (f)case alternatives are composed only of
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
  \item lambda abstractions,
  \item let expressions, and
  \item (f)case expressions.
  \end{itemize}
\item Patterns in case expressions (but not in fcase expressions) are
  restricted further in that all arguments of a constructor pattern
  are variable patterns.
\item Applications $N\:x$ in patterns and expressions, where $N$ is a
  newtype constructor, are replaced by a $x$. Note that neither the
  newtype declaration itself nor partial applications of newtype
  constructors are changed.\footnote{It would be possible to replace
  partial applications of newtype constructor by \texttt{Prelude.id}.
  However, our solution yields a more accurate output when the result
  of a computation includes partial applications.}
\end{itemize}

\ToDo{Use a different representation for the restricted code instead
of using the syntax tree from \texttt{Curry}.}

\textbf{As we are going to insert references to real Prelude entities,
all names must be properly qualified before calling this module.}
\begin{verbatim}

> module Desugar(desugar,goalModule) where
> import Base
> import Combined
> import Curry
> import CurryUtils
> import List
> import Monad
> import PredefIdent
> import PredefTypes
> import Ratio
> import TopEnv
> import Types
> import TypeInfo
> import Typing
> import Utils
> import ValueInfo

\end{verbatim}
New identifiers may be introduced while desugaring pattern
declarations, case expressions, and list comprehensions. As usual, we
use a state monad transformer for generating unique names. In
addition, the state is also used for passing through the type
environment, which must be augmented with the types of these new
variables.
\begin{verbatim}

> type DesugarState a = StateT ValueEnv (ReaderT TCEnv (StateT Int Id)) a

> run :: DesugarState a -> TCEnv -> ValueEnv -> a
> run m tcEnv tyEnv = runSt (callRt (callSt m tyEnv) tcEnv) 1

\end{verbatim}
The desugaring phase keeps only the type, function, and value
declarations of the module. As type declarations are not desugared and
cannot occur in local declaration groups they are filtered out
separately.

Actually, the transformation is slightly more general than necessary,
as it allows pattern and free variable declarations at the top-level
of a module.
\begin{verbatim}

> desugar :: TCEnv -> ValueEnv -> Module Type -> (Module Type,ValueEnv)
> desugar tcEnv tyEnv (Module m es is ds) = (Module m es is ds',tyEnv')
>   where (ds',tyEnv') = run (desugarModule m tyEnv ds) tcEnv tyEnv

> desugarModule :: ModuleIdent -> ValueEnv -> [TopDecl Type]
>               -> DesugarState ([TopDecl Type],ValueEnv)
> desugarModule m tyEnv ds =
>   do
>     dss' <- mapM (desugarTopDecl m tyEnv) tds
>     vds' <- desugarDeclGroup m [d | BlockDecl d <- vds]
>     tyEnv' <- fetchSt
>     return (concat dss' ++ map BlockDecl vds',tyEnv')
>   where (vds,tds) = partition isBlockDecl ds

\end{verbatim}
Goals are desugared by converting them into a module containing just a
single function declaration and desugaring the resulting module.
Goals with type \texttt{IO \_} are executed directly by the runtime
system. All other goals are evaluated under control of an interactive
top-level, which displays the solutions of the goal and in particular
the bindings of the free variables. For this reason, the free
variables declared in the \texttt{where} clause of a goal are
translated into free variables of the goal. In addition, the goal is
transformed into a first order expression by performing a unification
with another variable. Thus, a goal
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
where $v_0$ is a fresh variable. No variables are lifted at present
when generating code for the declarative debugger, since the debugger
evaluates the goal within an encapsulated search and we cannot pass
functions with arbitrary arity to the encapsulated search primitive.
In addition, the debugger currently lacks support for showing the
bindings of the goal's free variables.
\begin{verbatim}

> goalModule :: Bool -> ValueEnv -> ModuleIdent -> Ident -> Goal Type
>            -> (Maybe [Ident],Module Type,ValueEnv)
> goalModule debug tyEnv m g (Goal p e ds)
>   | isIO ty =
>       (Nothing,
>        mkModule m p g [] (mkLet ds e),
>        bindFun m g 0 (polyType ty) tyEnv)
>   | otherwise =
>       (if debug then Nothing else Just vs,
>        mkModule m p g (zip (ty:tys) (v0:vs))
>                 (apply (prelUnif ty) [mkVar ty v0,e']),
>        bindFun m v0 0 (monoType ty) (bindFun m g n (polyType ty') tyEnv))
>   where ty = typeOf e
>         v0 = anonId
>         (vs,e') = liftGoalVars debug (mkLet ds e)
>         tys = [rawType (varType v tyEnv) | v <- vs]
>         ty' = foldr TypeArrow successType (ty:tys)
>         n = 1 + length vs
>         isIO (TypeApply (TypeConstructor tc) _) = tc == qIOId
>         isIO _ = False

> mkModule :: ModuleIdent -> Position -> Ident -> [(a,Ident)] -> Expression a
>          -> Module a
> mkModule m p g vs e =
>    Module m Nothing []
>           [BlockDecl (funDecl p g (map (uncurry VariablePattern) vs) e)]

> liftGoalVars :: Bool -> Expression a -> ([Ident],Expression a)
> liftGoalVars debug (Let ds e)
>   | not debug = (concat [vs | FreeDecl _ vs <- vds],mkLet ds' e)
>   where (vds,ds') = partition isFreeDecl ds
> liftGoalVars _ e = ([],e)

\end{verbatim}
At the top-level of a module, we introduce the selector function of
each field label defined in that module. In addition, we have to
desugar the method declarations of each class and instance
declaration.

\ToDo{Instantiate quantified type variables in the types of the
  arguments of the selector functions with fresh type variables.}
\begin{verbatim}

> desugarTopDecl :: ModuleIdent -> ValueEnv -> TopDecl Type
>                -> DesugarState [TopDecl Type]
> desugarTopDecl m tyEnv (DataDecl p cx tc tvs cs clss) =
>   do
>     ds' <-
>       mapM (selectorDecl m tyEnv p (map (qualifyWith m . constr) cs))
>            (nub (concatMap labels cs))
>     return (DataDecl p cx tc tvs cs clss : map BlockDecl ds')
> desugarTopDecl m tyEnv (NewtypeDecl p cx tc tvs nc clss) =
>   do
>     ds' <- newSelectorDecl m tyEnv p (qualifyWith m (nconstr nc))
>     return (NewtypeDecl p cx tc tvs nc clss : map BlockDecl ds')
> desugarTopDecl _ _ (TypeDecl p tc tvs ty) = return [TypeDecl p tc tvs ty]
> desugarTopDecl m _ (ClassDecl p cx cls tv ds) =
>   do
>     vds' <- desugarDeclGroup m vds
>     return [ClassDecl p cx cls tv (tds ++ vds')]
>   where (tds,vds) = partition isTypeSig ds
> desugarTopDecl m _ (InstanceDecl p cx cls ty ds) =
>   do
>     ds' <- desugarDeclGroup m ds
>     return [InstanceDecl p cx cls ty ds']
> desugarTopDecl _ _ (DefaultDecl p tys) = return [DefaultDecl p tys]

> selectorDecl :: ModuleIdent -> ValueEnv -> Position -> [QualIdent] -> Ident
>              -> DesugarState (Decl Type)
> selectorDecl m tyEnv p cs l =
>   liftM (matchDecl p l . concat) (mapM (selectorEqn m tyEnv l) cs)

> selectorEqn :: ModuleIdent -> ValueEnv -> Ident -> QualIdent
>             -> DesugarState [(ConstrTerm Type,Expression Type)]
> selectorEqn m tyEnv l c =
>   case elemIndex l ls of
>     Just n ->
>       do
>         vs <- mapM (freshVar m "_#rec") tys
>         return [(constrPattern ty0 c vs,uncurry mkVar (vs!!n))]
>     Nothing -> return []
>   where (ls,_,ty) = conType c tyEnv
>         (tys,ty0) = arrowUnapply (rawType ty)

> newSelectorDecl :: ModuleIdent -> ValueEnv -> Position -> QualIdent
>                 -> DesugarState [Decl Type]
> newSelectorDecl m tyEnv p c
>   | l /= anonId =
>       do
>         v <- freshVar m "_#rec" (head (arrowArgs (rawType ty)))
>         return [funDecl p l [uncurry VariablePattern v] (uncurry mkVar v)]
>   | otherwise = return []
>   where (l:_,_,ty) = conType c tyEnv

\end{verbatim}
Within a local declaration group, all fixity declarations, type
signatures and trust annotations are discarded. First, the patterns
occurring in the left hand sides are desugared. Due to lazy patterns
this may add further declarations to the group that must be desugared
as well.
\begin{verbatim}

> desugarDeclGroup :: ModuleIdent -> [Decl Type] -> DesugarState [Decl Type]
> desugarDeclGroup m ds =
>   do
>     dss' <- mapM (desugarDeclLhs m) (filter isValueDecl ds)
>     mapM (desugarDeclRhs m) (concat dss')

> desugarDeclLhs :: ModuleIdent -> Decl Type -> DesugarState [Decl Type]
> desugarDeclLhs m (PatternDecl p t rhs) =
>   do
>     (ds',t') <- desugarTerm m p [] t
>     dss' <- mapM (desugarDeclLhs m) ds'
>     return (PatternDecl p t' rhs : concat dss')
> desugarDeclLhs _ d = return [d]

\end{verbatim}
The import entity specification of foreign functions using the
\texttt{ccall} and \texttt{rawcall} calling conventions is expanded to
always include the kind of the declaration (either \texttt{static} or
\texttt{dynamic}) and the name of the imported function.
\begin{verbatim}

> desugarDeclRhs :: ModuleIdent -> Decl Type -> DesugarState (Decl Type)
> desugarDeclRhs m (FunctionDecl p f eqs) =
>   liftM (FunctionDecl p f) (mapM (desugarEquation m) eqs)
> desugarDeclRhs _ (ForeignDecl p cc s ie f ty) =
>   return (ForeignDecl p cc (s `mplus` Just Safe) (desugarImpEnt cc ie) f ty)
>   where desugarImpEnt cc ie
>           | cc == CallConvPrimitive = ie `mplus` Just (name f)
>           | otherwise = Just (unwords (kind (maybe [] words ie)))
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
>         ident _ = internalError "desugarImpEnt"
> desugarDeclRhs m (PatternDecl p t rhs) =
>   liftM (PatternDecl p t) (desugarRhs m p rhs)
> desugarDeclRhs _ (FreeDecl p vs) = return (FreeDecl p vs)

> desugarEquation :: ModuleIdent -> Equation Type
>                 -> DesugarState (Equation Type)
> desugarEquation m (Equation p lhs rhs) =
>   do
>     (ds',ts') <- mapAccumM (desugarTerm m p) [] ts
>     rhs' <- desugarRhs m p (addDecls ds' rhs)
>     return (Equation p (FunLhs f ts') rhs')
>   where (f,ts) = flatLhs lhs

\end{verbatim}
The transformation of patterns is straightforward except for lazy
patterns. A lazy pattern \texttt{\~}$t$ is replaced by a fresh
variable $v$ and a new local declaration $t$~\texttt{=}~$v$ in the
scope of the pattern. In addition, as-patterns $v$\texttt{@}$t$ where
$t$ is a variable or an as-pattern are replaced by $t$ in combination
with a local declaration for $v$.
\begin{verbatim}

> desugarLiteralTerm :: Type -> Literal
>                    -> Either (ConstrTerm Type) (ConstrTerm Type)
> desugarLiteralTerm ty (Char c) = Right (LiteralPattern ty (Char c))
> desugarLiteralTerm ty (Integer i) =
>   Right (LiteralPattern ty (fixLiteral ty i))
>   where fixLiteral (TypeConstrained tys _) = fixLiteral (head tys)
>         fixLiteral ty
>           | ty == floatType = Rational . toRational
>           | otherwise = Integer
> desugarLiteralTerm ty (Rational r) = Right (LiteralPattern ty (Rational r))
> desugarLiteralTerm ty (String cs) =
>   Left (ListPattern ty (map (LiteralPattern (elemType ty) . Char) cs))

> desugarTerm :: ModuleIdent -> Position -> [Decl Type] -> ConstrTerm Type
>             -> DesugarState ([Decl Type],ConstrTerm Type)
> desugarTerm m p ds (LiteralPattern ty l) =
>   either (desugarTerm m p ds) (return . (,) ds) (desugarLiteralTerm ty l)
> desugarTerm m p ds (NegativePattern ty l) =
>   desugarTerm m p ds (LiteralPattern ty (negateLiteral l))
>   where negateLiteral (Integer i) = Integer (-i)
>         negateLiteral (Rational r) = Rational (-r)
>         negateLiteral _ = internalError "negateLiteral"
> desugarTerm _ _ ds (VariablePattern ty v) = return (ds,VariablePattern ty v)
> desugarTerm m p ds (ConstructorPattern ty c [t]) =
>   do
>     tyEnv <- fetchSt
>     liftM (if isNewtypeConstr tyEnv c then id else apSnd (constrPat ty c))
>           (desugarTerm m p ds t)
>   where constrPat ty c t = ConstructorPattern ty c [t]
> desugarTerm m p ds (ConstructorPattern ty c ts) =
>   liftM (apSnd (ConstructorPattern ty c)) (mapAccumM (desugarTerm m p) ds ts)
> desugarTerm m p ds (InfixPattern ty t1 op t2) =
>   desugarTerm m p ds (ConstructorPattern ty op [t1,t2])
> desugarTerm m p ds (ParenPattern t) = desugarTerm m p ds t
> desugarTerm m p ds (RecordPattern ty c fs) =
>   do
>     (ls,tys) <- liftM (argumentTypes ty c) fetchSt
>     ts <- zipWithM argument tys (orderFields fs ls)
>     desugarTerm m p ds (ConstructorPattern ty c ts)
>   where argument ty = maybe (fresh ty) return
>         fresh ty = liftM (uncurry VariablePattern) (freshVar m "_#rec" ty)
> desugarTerm m p ds (TuplePattern ts) =
>   desugarTerm m p ds
>     (ConstructorPattern (tupleType (map typeOf ts)) (qTupleId (length ts)) ts)
> desugarTerm m p ds (ListPattern ty ts) =
>   liftM (apSnd (foldr cons nil)) (mapAccumM (desugarTerm m p) ds ts)
>   where nil = ConstructorPattern ty qNilId []
>         cons t ts = ConstructorPattern ty qConsId [t,ts]
> desugarTerm m p ds (AsPattern v t) =
>   liftM (desugarAs p v) (desugarTerm m p ds t)
> desugarTerm m p ds (LazyPattern t) = desugarLazy m p ds t

> desugarAs :: Position -> Ident -> ([Decl Type],ConstrTerm Type)
>           -> ([Decl Type],ConstrTerm Type)
> desugarAs p v (ds,t) =
>   case t of
>     VariablePattern ty v' -> (varDecl p ty v (mkVar ty v') : ds,t)
>     AsPattern v' t' -> (varDecl p ty v (mkVar ty v') : ds,t)
>       where ty = typeOf t'
>     _ -> (ds,AsPattern v t)

> desugarLazy :: ModuleIdent -> Position -> [Decl Type] -> ConstrTerm Type
>             -> DesugarState ([Decl Type],ConstrTerm Type)
> desugarLazy m p ds t =
>   case t of
>     VariablePattern _ _ -> return (ds,t)
>     ParenPattern t' -> desugarLazy m p ds t'
>     AsPattern v t' -> liftM (desugarAs p v) (desugarLazy m p ds t')
>     LazyPattern t' -> desugarLazy m p ds t'
>     _ ->
>       do
>         (ty,v') <- freshVar m "_#lazy" t
>         return (patDecl p t (mkVar ty v') : ds,VariablePattern ty v')

\end{verbatim}
A list of boolean guards is expanded into a nested if-then-else
expression, whereas a constraint guard is replaced by a case
expression. Note that if the guard type is \texttt{Success} only a
single guard is allowed for each equation.\footnote{This change was
introduced in version 0.8 of the Curry report.} We check whether the
guard's type is \texttt{Bool} because the type defaults to
\texttt{Success} if it is not restricted by the guard expression.
\begin{verbatim}

> desugarRhs :: ModuleIdent -> Position -> Rhs Type -> DesugarState (Rhs Type)
> desugarRhs m p rhs =
>   do
>     e' <- desugarExpr m p (expandRhs (prelFailed (typeOf rhs)) rhs)
>     return (SimpleRhs p e' [])

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

> desugarLiteral :: Type -> Literal
>                -> Either (Expression Type) (Expression Type)
> desugarLiteral ty (Char c) = Right (Literal ty (Char c))
> desugarLiteral ty (Integer i) = Right (fixLiteral ty i)
>   where fixLiteral (TypeConstrained tys _) = fixLiteral (head tys)
>         fixLiteral ty'
>           | ty' `elem` [intType,integerType] = Literal ty . Integer
>           | ty' == floatType = Literal ty . Rational . fromInteger
>           | ty' == rationalType = desugarRatio . fromInteger
>           | otherwise =
>               Apply (prelFromInteger ty) . Literal integerType . Integer
> desugarLiteral ty (Rational r) = Right (fixLiteral ty r)
>   where fixLiteral (TypeConstrained tys _) = fixLiteral (head tys)
>         fixLiteral ty'
>           | ty' == floatType = Literal ty . Rational
>           | ty' == rationalType = desugarRatio
>           | otherwise = Apply (prelFromRational ty) . desugarRatio
> desugarLiteral ty (String cs) =
>   Left (List ty (map (Literal (elemType ty) . Char) cs))

> desugarRatio :: Rational -> Expression Type
> desugarRatio r =
>   foldl applyToInteger (ratioConstr integerType) [numerator r,denominator r]
>   where applyToInteger e = Apply e . Literal integerType . Integer

> desugarExpr :: ModuleIdent -> Position -> Expression Type
>             -> DesugarState (Expression Type)
> desugarExpr m p (Literal ty l) =
>   either (desugarExpr m p) return (desugarLiteral ty l)
> desugarExpr m p (Variable ty v)
>   -- NB The name of the initial goal is anonId (not renamed, cf. goalModule
>   --    above) and must not be changed
>   | isRenamed v' && unRenameIdent v' == anonId =
>       do
>         v'' <- freshVar m "_#var" ty
>         return (Let [FreeDecl p [snd v'']] (uncurry mkVar v''))
>   | otherwise = return (Variable ty v)
>   where v' = unqualify v
> desugarExpr _ _ (Constructor ty c) = return (Constructor ty c)
> desugarExpr m p (Paren e) = desugarExpr m p e
> desugarExpr m p (Typed e _) = desugarExpr m p e
> desugarExpr m p (Record ty c fs) =
>   do
>     (ls,tys) <- liftM (argumentTypes ty c) fetchSt
>     let es = zipWith argument tys (orderFields fs ls)
>     desugarExpr m p (applyConstr ty c tys es)
>   where argument ty = maybe (prelUndefined ty) id
> desugarExpr m p (RecordUpdate e fs) =
>   do
>     tyEnv <- fetchSt
>     f <- freshIdent m "_#upd" 1 (polyType ty')
>     cs <- liftM (constructors tc) (liftSt envRt)
>     eqs <- mapM (updateEqn m tyEnv . qualifyLike tc) cs
>     desugarExpr m p (Let [matchDecl p f (concat eqs)] (Apply (mkVar ty' f) e))
>   where ty = typeOf e
>         ty' = TypeArrow ty ty
>         tc = rootOfType (arrowBase ty)
>         ls = [unqualify l | Field l _ <- fs]
>         updateEqn m tyEnv c
>           | all (`elem` ls') ls =
>               do
>                 vs <- mapM (freshVar m "_#rec") tys
>                 let es = zipWith argument vs (orderFields fs ls')
>                 return [(constrPattern ty c vs,applyConstr ty c tys es)]
>           | otherwise = return []
>           where (ls',tys) = argumentTypes ty c tyEnv
>         argument v = maybe (uncurry mkVar v) id
> desugarExpr m p (Tuple es) =
>   liftM (apply (Constructor (foldr TypeArrow (tupleType tys) tys)
>                             (qTupleId (length es))))
>         (mapM (desugarExpr m p) es)
>   where tys = map typeOf es
> desugarExpr m p (List ty es) =
>   liftM (foldr cons nil) (mapM (desugarExpr m p) es)
>   where nil = Constructor ty qNilId
>         cons = Apply . Apply (Constructor (consType (elemType ty)) qConsId)
> desugarExpr m p (ListCompr e []) =
>   desugarExpr m p (List (listType (typeOf e)) [e])
> desugarExpr m p (ListCompr e (q:qs)) = desugarQual m p q (ListCompr e qs)
> desugarExpr m p (EnumFrom e) =
>   liftM (Apply (prelEnumFrom (typeOf e))) (desugarExpr m p e)
> desugarExpr m p (EnumFromThen e1 e2) =
>   liftM (apply (prelEnumFromThen (typeOf e1)))
>         (mapM (desugarExpr m p) [e1,e2])
> desugarExpr m p (EnumFromTo e1 e2) =
>   liftM (apply (prelEnumFromTo (typeOf e1))) (mapM (desugarExpr m p) [e1,e2])
> desugarExpr m p (EnumFromThenTo e1 e2 e3) =
>   liftM (apply (prelEnumFromThenTo (typeOf e1)))
>         (mapM (desugarExpr m p) [e1,e2,e3])
> desugarExpr m p (UnaryMinus e) =
>   liftM (Apply (prelNegate (typeOf e))) (desugarExpr m p e)
> desugarExpr m p (Apply (Constructor ty c) e) =
>   do
>     tyEnv <- fetchSt
>     liftM (if isNewtypeConstr tyEnv c then id else (Apply (Constructor ty c)))
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
>     return (Apply (Apply (prelFlip ty1 ty2 ty3) op') e')
>   where TypeArrow ty1 (TypeArrow ty2 ty3) = typeOf (infixOp op)
> desugarExpr m _ (Lambda p ts e) =
>   do
>     (ds',ts') <- mapAccumM (desugarTerm m p) [] ts
>     e' <- desugarExpr m p (mkLet ds' e)
>     return (Lambda p ts' e')
> desugarExpr m p (Let ds e) =
>   do
>     ds' <- desugarDeclGroup m ds
>     e' <- desugarExpr m p e
>     return (mkLet ds' e')
> desugarExpr m p (Do sts e) = desugarExpr m p (foldr desugarStmt e sts)
>   where desugarStmt (StmtExpr e) e' =
>           apply (prelBind_ (typeOf e) (typeOf e')) [e,e']
>         desugarStmt (StmtBind p t e) e' =
>           apply (prelBind (typeOf e) (typeOf t) (typeOf e'))
>                 [e,Lambda p [t] e']
>         desugarStmt (StmtDecl ds) e' = mkLet ds e'
> desugarExpr m p (IfThenElse e1 e2 e3) =
>   do
>     e1' <- desugarExpr m p e1
>     e2' <- desugarExpr m p e2
>     e3' <- desugarExpr m p e3
>     return (Case e1' [caseAlt p truePattern e2',caseAlt p falsePattern e3'])
> desugarExpr m p (Case e alts) =
>   do
>     v <- freshVar m "_#case" e
>     e' <- desugarExpr m p e
>     liftM (mkCase m v e') 
>           (mapM (liftM fromAlt . desugarAltLhs m) alts >>=
>            desugarCase m (typeOf (Case e alts)) id [v])
>   where ts = [t | Alt p t rhs <- alts]
>         fromAlt (Alt p t rhs) = (p,id,[t],rhs)
>         mkCase m (_,v) e (Case e' alts)
>           | mkVar (typeOf e') v == e' && v `notElem` qfv m alts = Case e alts
>         mkCase _ (ty,v) e e' = Let [varDecl p ty v e] e'
> desugarExpr m p (Fcase e alts) =
>   liftM2 Fcase (desugarExpr m p e) (mapM (desugarFcaseAlt m) alts)

> desugarFcaseAlt :: ModuleIdent -> Alt Type -> DesugarState (Alt Type)
> desugarFcaseAlt m (Alt p t rhs) =
>   do
>     (ds',t') <- desugarTerm m p [] t
>     rhs' <- desugarRhs m p (addDecls ds' rhs)
>     return (Alt p t' rhs')

\end{verbatim}
Rigid case expressions, but not flexible fcase expressions, with
nested patterns are transformed into nested case expressions where
each expression uses only flat patterns. The algorithm used here is a
variant of the algorithm used for transforming pattern matching of
function heads and flexible case expressions into intermediate
language case expressions (see Sect.~\ref{sec:il-trans}). In contrast
to the algorithm presented in Sect.~5 of~\cite{PeytonJones87:Book},
the code generated by our algorithm will not perform redundant
matches. Furthermore, we do not need a special pattern match failure
primitive and fatbar expressions in order to catch such failures. On
the other hand, our algorithm can cause code duplication. We do not
care about that because most pattern matching in Curry programs occurs
in function heads and not in case expressions.

The essential difference between pattern matching in rigid case
expressions on one hand and function heads and flexible fcase
expressions on the other hand is that in case expressions,
alternatives are matched from top to bottom and evaluation commits to
the first alternative with a matching pattern. If an alternative uses
boolean guards and all guards of that alternative fail, pattern
matching continues with the next alternative as if the pattern did not
match. As an extension, we also support constraint guards, but no fall
through behavior applies to such guards since it cannot be implemented
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

> type Match a =
>   (Position,[ConstrTerm a] -> [ConstrTerm a],[ConstrTerm a],Rhs a)

> pattern :: (Type,Ident) -> ConstrTerm Type -> ConstrTerm Type
> pattern (ty,v) (LiteralPattern _ l) = AsPattern v (LiteralPattern ty l)
> pattern (ty,v) (VariablePattern _ _) = VariablePattern ty v
> pattern (ty,v) (ConstructorPattern _ c ts) =
>   AsPattern v (ConstructorPattern ty c ts')
>   where ts' = [VariablePattern (typeOf t) anonId | t <- ts]
> pattern v (AsPattern _ t) = pattern v t

> arguments :: ConstrTerm a -> [ConstrTerm a]
> arguments (LiteralPattern _ _) = []
> arguments (VariablePattern _ _) = []
> arguments (ConstructorPattern _ _ ts) = ts
> arguments (AsPattern _ t) = arguments t

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

> bindVars :: Position -> (Type,Ident) -> ConstrTerm Type -> Rhs Type
>          -> Rhs Type
> bindVars _ _ (LiteralPattern _ _) = id
> bindVars p (ty,v) (VariablePattern ty' v')
>   | v /= v' = addDecls [varDecl p ty' v' (mkVar ty v)]
>   | otherwise = id
> bindVars _ _ (ConstructorPattern _ _ _) = id
> bindVars p (ty,v) (AsPattern v' t) =
>   addDecls [varDecl p ty v' (mkVar ty v)] . bindVars p (ty,v) t

> desugarAltLhs :: ModuleIdent -> Alt Type -> DesugarState (Alt Type)
> desugarAltLhs m (Alt p t rhs) =
>   do
>     (ds',t') <- desugarTerm m p [] t
>     return (Alt p t' (addDecls ds' rhs))

> desugarAltRhs :: ModuleIdent -> Alt Type -> Expression Type
>               -> DesugarState (Expression Type)
> desugarAltRhs m (Alt p _ rhs) e0 = desugarExpr m p (expandRhs e0 rhs)

> desugarCase :: ModuleIdent -> Type -> ([(Type,Ident)] -> [(Type,Ident)])
>             -> [(Type,Ident)] -> [Match Type]
>             -> DesugarState (Expression Type)
> desugarCase _ ty _ _ [] = return (prelFailed ty)
> desugarCase m ty prefix [] (alt : alts) =
>   desugarCase m ty id vs (map resetArgs alts) >>=
>   desugarAltRhs m (toAlt vs alt)
>   where vs = prefix []
>         resetArgs (p,prefix,ts,rhs) = (p,id,prefix ts,rhs)
>         toAlt vs (p,prefix,_,rhs) =
>           Alt p (VariablePattern (TypeVariable 0) anonId)
>               (foldr2 (bindVars p) rhs vs (prefix []))
> desugarCase m ty prefix (v:vs) alts =
>   case fst (head alts') of
>     VariablePattern _ _
>       | all isVarPattern (map fst (tail alts')) ->
>           desugarCase m ty prefix vs (map dropArg alts)
>       | otherwise -> desugarCase m ty (prefix . (v:)) vs (map skipArg alts)
>     t'@(AsPattern _ (LiteralPattern ty' l'))
>       | fst v `elem` (charType:numTypes) ->
>           liftM (Case (uncurry mkVar v))
>                 (mapM (desugarCaseAlt m ty prefix vs alts') (lts ++ vts))
>       | otherwise ->
>           liftM (Case (equal v (desugarLiteral ty' l')))
>                 (sequence [desugarLitAlt True m ty prefix (v:vs) alts' t',
>                            desugarLitAlt False m ty prefix (v:vs) alts' t'])
>     AsPattern _ (ConstructorPattern _ _ _)
>       | null lts ->
>           do
>             tcEnv <- liftSt envRt
>             liftM (Case (uncurry mkVar v))
>                   (mapM (desugarCaseAlt m ty prefix vs alts')
>                         (cts ++ if allCases tcEnv v cts then [] else vts))
>       | otherwise ->
>           desugarCase m ty (prefix . (v:)) (v:vs) (map dupArg alts)
>   where alts' = map tagAlt alts
>         (lts,cts,vts) = partitionPatterns (nub (map fst alts'))
>         tagAlt (p,prefix,t:ts,rhs) =
>           (pattern v t,(p,prefix,t:ts,bindVars p v t rhs))
>         skipArg (p,prefix,t:ts,rhs) = (p,prefix . (t:),ts,rhs)
>         dropArg (p,prefix,t:ts,rhs) = (p,prefix,ts,bindVars p v t rhs)
>         equal v (Right e) = apply (prelEq (fst v)) [uncurry mkVar v,e]
>         allCases tcEnv (ty,_) ts = length cs == length ts
>           where cs = constructors (rootOfType ty) tcEnv
>         dupArg (p,prefix,t:ts,rhs) =
>           (p,prefix . (asLiteral v t :),asConstrApp v t:ts,rhs)

> partitionPatterns :: [ConstrTerm a]
>                   -> ([ConstrTerm a],[ConstrTerm a],[ConstrTerm a])
> partitionPatterns = foldr partition ([],[],[])
>   where partition t@(AsPattern _ (LiteralPattern _ _)) ~(lts,cts,vts) =
>           (t:lts,cts,vts)
>         partition t@(VariablePattern _ _) ~(lts,cts,vts) = (lts,cts,t:vts)
>         partition t@(AsPattern _ (ConstructorPattern _ _ _)) ~(lts,cts,vts) =
>           (lts,t:cts,vts)

> desugarCaseAlt :: ModuleIdent -> Type -> ([(Type,Ident)] -> [(Type,Ident)])
>                -> [(Type,Ident)] -> [(ConstrTerm Type,Match Type)]
>                -> ConstrTerm Type -> DesugarState (Alt Type)
> desugarCaseAlt m ty prefix vs alts t =
>   do
>     vs' <- mapM (freshVar m "_#case") (arguments t)
>     liftM (caseAlt (pos (head alts')) (renameArgs vs' t))
>           (desugarCase m ty id (prefix (vs' ++ vs))
>                        (map (expandArgs vs') alts'))
>   where alts' = [alt | (t',alt) <- alts, t' == t || isVarPattern t']
>         pos (p,_,_,_) = p
>         expandArgs vs (p,prefix,t:ts,rhs) =
>           (p,id,prefix (expandPatternArgs vs t ++ ts),rhs)
>         expandPatternArgs vs t
>           | isVarPattern t = map (uncurry VariablePattern) vs
>           | otherwise = arguments t

> desugarLitAlt :: Bool -> ModuleIdent -> Type
>               -> ([(Type,Ident)] -> [(Type,Ident)]) -> [(Type,Ident)]
>               -> [(ConstrTerm Type,Match Type)] -> ConstrTerm Type
>               -> DesugarState (Alt Type)
> desugarLitAlt eq m ty prefix vs alts t =
>   liftM (caseAlt (pos (head alts')) t')
>         (desugarCase m ty id (prefix vs) (map resetArgs alts'))
>   where v = head vs
>         t' = if eq then truePattern else falsePattern
>         alts'
>           | eq = [if t == t' then matchArg v alt else alt | (t',alt) <- alts]
>           | otherwise = [alt | (t',alt) <- alts, t /= t']
>         pos (p,_,_,_) = p
>         matchArg v (p,prefix,t:ts,rhs) = (p,prefix,asConstrApp v t:ts,rhs)
>         resetArgs (p,prefix,ts,rhs) = (p,id,prefix ts,rhs)

> renameArgs :: [(Type,Ident)] -> ConstrTerm Type -> ConstrTerm Type
> renameArgs _ (LiteralPattern ty l) = LiteralPattern ty l
> renameArgs _ (VariablePattern ty v) = VariablePattern ty v
> renameArgs vs (ConstructorPattern ty c _) =
>   ConstructorPattern ty c (map (uncurry VariablePattern) vs)
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
equivalent Prelude function \texttt{concatMap}. In addition, if the
remaining list comprehension in the body of the auxiliary function has
no qualifiers -- i.e., if it is equivalent to \texttt{[$e$]} -- we
avoid the construction of the singleton list by calling \texttt{(:)}
instead of \texttt{(++)} and \texttt{map} in place of
\texttt{concatMap}, respectively.
\begin{verbatim}

> desugarQual :: ModuleIdent -> Position -> Statement Type -> Expression Type
>             -> DesugarState (Expression Type)
> desugarQual m p (StmtExpr b) e =
>   desugarExpr m p (IfThenElse b e (List (typeOf e) []))
> desugarQual m _ (StmtBind p t l) e
>   | isVarPattern t = desugarExpr m p (qualExpr t e l)
>   | otherwise =
>       do
>         (ty,v) <- freshVar m "_#var" t
>         (ty',l') <- freshVar m "_#var" e
>         desugarExpr m p
>           (apply (prelFoldr ty ty') [foldFunct ty v ty' l' e,List ty' [],l])
>   where qualExpr v (ListCompr e []) l =
>           apply (prelMap (typeOf v) (typeOf e)) [Lambda p [v] e,l]
>         qualExpr v e l =
>           apply (prelConcatMap (typeOf v) (elemType (typeOf e)))
>                 [Lambda p [v] e,l]
>         foldFunct ty v ty' l e =
>           Lambda p [VariablePattern ty v,VariablePattern ty' l]
>             (Case (mkVar ty v)
>                   [caseAlt p t (append (elemType ty') e (mkVar ty' l)),
>                    caseAlt p (VariablePattern ty v) (mkVar ty' l)])
>         append ty (ListCompr e []) l =
>           apply (Constructor (consType ty) qConsId) [e,l]
>         append ty e l = apply (prelAppend ty) [e,l]
> desugarQual m p (StmtDecl ds) e = desugarExpr m p (mkLet ds e)

\end{verbatim}
Generation of fresh names
\begin{verbatim}

> freshIdent :: ModuleIdent -> String -> Int -> TypeScheme -> DesugarState Ident
> freshIdent m prefix n ty =
>   do
>     x <- liftM (mkName prefix) (liftSt (liftRt (updateSt (1 +))))
>     updateSt_ (bindFun m x n ty)
>     return x
>   where mkName pre n = mkIdent (pre ++ show n)

> freshVar :: Typeable a => ModuleIdent -> String -> a
>          -> DesugarState (Type,Ident)
> freshVar m prefix x =
>   do
>     v <- freshIdent m prefix 0 (monoType ty)
>     return (ty,v)
>   where ty = typeOf x

\end{verbatim}
Prelude entities
\begin{verbatim}

> prelUndefined a = preludeFun [] a "undefined"
> prelUnif a = preludeFun [a,a] successType "=:="
> prelFromInteger a = preludeFun [integerType] a "fromInteger"
> prelFromRational a = preludeFun [rationalType] a "fromRational"
> prelEq a = preludeFun [a,a] boolType "=="
> prelBind ma a mb = preludeFun [ma,a `TypeArrow` mb] mb ">>="
> prelBind_ ma mb = preludeFun [ma,mb] mb ">>"
> prelFlip a b c = preludeFun [a `TypeArrow` (b `TypeArrow` c),b,a] c "flip"
> prelEnumFrom a = preludeFun [a] (listType a) "enumFrom"
> prelEnumFromTo a = preludeFun [a,a] (listType a) "enumFromTo"
> prelEnumFromThen a = preludeFun [a,a] (listType a) "enumFromThen"
> prelEnumFromThenTo a = preludeFun [a,a,a] (listType a) "enumFromThenTo"
> prelFailed a = preludeFun [] a "failed"
> prelMap a b = preludeFun [a `TypeArrow` b,listType a] (listType b) "map"
> prelFoldr a b =
>   preludeFun [a `TypeArrow` (b `TypeArrow` b),b,listType a] b "foldr"
> prelAppend a = preludeFun [listType a,listType a] (listType a) "++"
> prelConcatMap a b =
>   preludeFun [a `TypeArrow` listType b] (listType a `TypeArrow` listType b)
>              "concatMap"
> prelNegate a = preludeFun [a] a "negate"

> preludeFun :: [Type] -> Type -> String -> Expression Type
> preludeFun tys ty f =
>   Variable (foldr TypeArrow ty tys) (qualifyWith preludeMIdent (mkIdent f))

> ratioConstr a =
>   Constructor (TypeArrow a (TypeArrow a (ratioType a)))
>               (qualifyWith ratioMIdent (mkIdent ":%"))

> truePattern = ConstructorPattern boolType qTrueId []
> falsePattern = ConstructorPattern boolType qFalseId []
> successPattern = ConstructorPattern successType qSuccessId []

\end{verbatim}
Auxiliary definitions
\begin{verbatim}

> addDecls :: [Decl a] -> Rhs a -> Rhs a
> addDecls ds (SimpleRhs p e ds') = SimpleRhs p e (ds ++ ds')
> addDecls ds (GuardedRhs es ds') = GuardedRhs es (ds ++ ds')

> consType :: Type -> Type
> consType a = TypeArrow a (TypeArrow (listType a) (listType a))

> elemType :: Type -> Type
> elemType (TypeApply (TypeConstructor tc) ty) | tc == qListId = ty
> elemType ty = internalError ("elemType " ++ show ty)

> ioResType :: Type -> Type
> ioResType (TypeApply (TypeConstructor tc) ty) | tc == qIOId = ty
> ioResType ty = internalError ("ioResType " ++ show ty)

> matchDecl :: Position -> Ident -> [(ConstrTerm a,Expression a)] -> Decl a
> matchDecl p f eqs = FunctionDecl p f [funEqn p f [t] e | (t,e) <- eqs]

> constrPattern :: a -> QualIdent -> [(a,Ident)] -> ConstrTerm a
> constrPattern ty c vs =
>   ConstructorPattern ty c (map (uncurry VariablePattern) vs)

> applyConstr :: Type -> QualIdent -> [Type] -> [Expression Type]
>             -> Expression Type
> applyConstr ty c tys = apply (Constructor (foldr TypeArrow ty tys) c)

\end{verbatim}
