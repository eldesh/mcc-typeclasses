% -*- LaTeX -*-
% $Id: Desugar.lhs 2798 2009-04-26 15:29:05Z wlux $
%
% Copyright (c) 2001-2009, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Desugar.lhs}
\section{Desugaring Curry Expressions}\label{sec:desugar}
The desugaring pass removes most syntactic sugar from the module. In
particular, the output of the desugarer will have the following
properties.
\begin{itemize}
\item Patterns in equations and (f)case alternatives are composed of only
  \begin{itemize}
  \item literals,
  \item variables,
  \item constructor applications, and
  \item as patterns.
  \end{itemize}
\item Expressions are composed of only
  \begin{itemize}
  \item literals,
  \item variables,
  \item constructors,
  \item (binary) applications,
  \item lambda abstractions,
  \item let expressions,
  \item if-then-else expressions, and
  \item (f)case expressions.
  \end{itemize}
\end{itemize}
Note that some syntactic sugar remains. In particular, we do not
replace boolean guards by if-then-else cascades and we do not
transform where clauses into let expressions. Both will happen only
after flattening patterns in case expressions, as this allows us to
handle the fall through behavior of boolean guards in case expressions
without introducing a special pattern match failure primitive (see
Sect.~\ref{sec:flatcase}). We also do not desugar if-then-else
expressions; the case matching phase will take care of that, too.

\textbf{As we are going to insert references to real Prelude entities,
all names must be properly qualified before calling this module.}
\begin{verbatim}

> module Desugar(desugar) where
> import Base
> import Combined
> import Curry
> import CurryUtils
> import List
> import Monad
> import PredefIdent
> import PredefTypes
> import Ratio
> import Types
> import TypeInfo
> import Typing
> import Utils
> import ValueInfo

\end{verbatim}
New identifiers may be introduced while desugaring pattern
declarations, record patterns and expressions, and list
comprehensions. As usual, we use a state monad transformer for
generating unique names. In addition, the state is also used for
passing through the type environment, which is augmented with the
types of the new variables.
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
> desugarTopDecl _ _ (SplitAnnot p) = return [SplitAnnot p]

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
>         v <- freshVar m "_#rec" (head tys)
>         return [funDecl p l [constrPattern ty0 c [v]] (uncurry mkVar v)]
>   | otherwise = return []
>   where (l:_,_,ty) = conType c tyEnv
>         (tys,ty0) = arrowUnapply (rawType ty)

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
>   liftM (PatternDecl p t) (desugarRhs m rhs)
> desugarDeclRhs _ (FreeDecl p vs) = return (FreeDecl p vs)

> desugarEquation :: ModuleIdent -> Equation Type
>                 -> DesugarState (Equation Type)
> desugarEquation m (Equation p lhs rhs) =
>   do
>     (ds',ts') <- mapAccumM (desugarTerm m p) [] ts
>     rhs' <- desugarRhs m (addDecls ds' rhs)
>     return (Equation p (FunLhs f ts') rhs')
>   where (f,ts) = flatLhs lhs

\end{verbatim}
The transformation of patterns is straightforward except for lazy
patterns. A lazy pattern \texttt{\~}$t$ is replaced by a fresh
variable $v$ and a new local declaration $t$~\texttt{=}~$v$ in the
scope of the pattern. In addition, an as-pattern $v$\texttt{@}$t$
where $t$ is a variable or an as-pattern is replaced by $t$ in
conjunction with a local declaration for $v$.
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
> desugarTerm m p ds (ConstructorPattern ty c ts) =
>   liftM (apSnd (ConstructorPattern ty c)) (mapAccumM (desugarTerm m p) ds ts)
> desugarTerm m p ds (InfixPattern ty t1 op t2) =
>   desugarTerm m p ds (ConstructorPattern ty op [t1,t2])
> desugarTerm m p ds (ParenPattern t) = desugarTerm m p ds t
> desugarTerm m p ds (RecordPattern ty c fs) =
>   do
>     tcEnv <- liftSt envRt
>     (ls,tys) <- liftM (argumentTypes tcEnv ty c) fetchSt
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

> desugarRhs :: ModuleIdent -> Rhs Type -> DesugarState (Rhs Type)
> desugarRhs m (SimpleRhs p e ds) =
>   do
>     ds' <- desugarDeclGroup m ds
>     e' <- desugarExpr m p e
>     return (SimpleRhs p e' ds')
> desugarRhs m (GuardedRhs es ds) =
>   do
>     ds' <- desugarDeclGroup m ds
>     es' <- mapM (desugarCondExpr m) es
>     return (GuardedRhs es' ds')

> desugarCondExpr :: ModuleIdent -> CondExpr Type
>                 -> DesugarState (CondExpr Type)
> desugarCondExpr m (CondExpr p g e) =
>   liftM2 (CondExpr p) (desugarExpr m p g) (desugarExpr m p e)

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
>     tcEnv <- liftSt envRt
>     (ls,tys) <- liftM (argumentTypes tcEnv ty c) fetchSt
>     let es = zipWith argument tys (orderFields fs ls)
>     desugarExpr m p (applyConstr ty c tys es)
>   where argument ty = maybe (prelUndefined ty) id
> desugarExpr m p (RecordUpdate e fs) =
>   do
>     tyEnv <- fetchSt
>     tcEnv <- liftSt envRt
>     f <- freshIdent m "_#upd" 1 (polyType ty')
>     eqs <-
>       mapM (updateEqn m tcEnv tyEnv . qualifyLike tc) (constructors tc tcEnv)
>     desugarExpr m p (Let [matchDecl p f (concat eqs)] (Apply (mkVar ty' f) e))
>   where ty = typeOf e
>         ty' = TypeArrow ty ty
>         tc = rootOfType (arrowBase ty)
>         ls = [unqualify l | Field l _ <- fs]
>         updateEqn m tcEnv tyEnv c
>           | all (`elem` ls') ls =
>               do
>                 vs <- mapM (freshVar m "_#rec") tys
>                 let es = zipWith argument vs (orderFields fs ls')
>                 return [(constrPattern ty c vs,applyConstr ty c tys es)]
>           | otherwise = return []
>           where (ls',tys) = argumentTypes tcEnv ty c tyEnv
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
> desugarExpr m p (Apply e1 e2) =
>   liftM2 Apply (desugarExpr m p e1) (desugarExpr m p e2)
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
>   liftM3 IfThenElse
>          (desugarExpr m p e1)
>          (desugarExpr m p e2)
>          (desugarExpr m p e3)
> desugarExpr m p (Case e as) =
>   liftM2 Case (desugarExpr m p e) (mapM (desugarAlt m) as)
> desugarExpr m p (Fcase e as) =
>   liftM2 Fcase (desugarExpr m p e) (mapM (desugarAlt m) as)

> desugarAlt :: ModuleIdent -> Alt Type -> DesugarState (Alt Type)
> desugarAlt m (Alt p t rhs) =
>   do
>     (ds',t') <- desugarTerm m p [] t
>     rhs' <- desugarRhs m (addDecls ds' rhs)
>     return (Alt p t' rhs')

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
> prelFromInteger a = preludeFun [integerType] a "fromInteger"
> prelFromRational a = preludeFun [rationalType] a "fromRational"
> prelBind ma a mb = preludeFun [ma,a `TypeArrow` mb] mb ">>="
> prelBind_ ma mb = preludeFun [ma,mb] mb ">>"
> prelFlip a b c = preludeFun [a `TypeArrow` (b `TypeArrow` c),b,a] c "flip"
> prelEnumFrom a = preludeFun [a] (listType a) "enumFrom"
> prelEnumFromTo a = preludeFun [a,a] (listType a) "enumFromTo"
> prelEnumFromThen a = preludeFun [a,a] (listType a) "enumFromThen"
> prelEnumFromThenTo a = preludeFun [a,a,a] (listType a) "enumFromThenTo"
> prelMap a b = preludeFun [a `TypeArrow` b,listType a] (listType b) "map"
> prelFoldr a b =
>   preludeFun [a `TypeArrow` (b `TypeArrow` b),b,listType a] b "foldr"
> prelAppend a = preludeFun [listType a,listType a] (listType a) "++"
> prelConcatMap a b =
>   preludeFun [a `TypeArrow` listType b,listType a] (listType b) "concatMap"
> prelNegate a = preludeFun [a] a "negate"

> preludeFun :: [Type] -> Type -> String -> Expression Type
> preludeFun tys ty f =
>   Variable (foldr TypeArrow ty tys) (qualifyWith preludeMIdent (mkIdent f))

> ratioConstr :: Type -> Expression Type
> ratioConstr a =
>   Constructor (TypeArrow a (TypeArrow a (ratioType a)))
>               (qualifyWith ratioMIdent (mkIdent ":%"))

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

> matchDecl :: Position -> Ident -> [(ConstrTerm a,Expression a)] -> Decl a
> matchDecl p f eqs = FunctionDecl p f [funEqn p f [t] e | (t,e) <- eqs]

> constrPattern :: a -> QualIdent -> [(a,Ident)] -> ConstrTerm a
> constrPattern ty c vs =
>   ConstructorPattern ty c (map (uncurry VariablePattern) vs)

> applyConstr :: Type -> QualIdent -> [Type] -> [Expression Type]
>             -> Expression Type
> applyConstr ty c tys = apply (Constructor (foldr TypeArrow ty tys) c)

\end{verbatim}
