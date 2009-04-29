% -*- LaTeX -*-
% $Id: Records.lhs 2809 2009-04-29 13:11:20Z wlux $
%
% Copyright (c) 2001-2009, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Records.lhs}
\section{Records and Field Labels}
As an extension to the Curry language the compiler supports Haskell's
record syntax, which introduces field labels for data and renaming
types. Field labels can be used in constructor declarations, patterns,
and expressions. For further convenience, an implicit selector
function is introduced for each field label. The code in this module
transforms the record notation into plain Curry code. Note that we
assume that most other syntactic sugar has been transformed already.
\begin{verbatim}

> module Records(unlabel) where
> import Combined
> import Curry
> import CurryUtils
> import List
> import Monad
> import PredefIdent
> import Types
> import TypeInfo
> import Typing
> import ValueInfo

\end{verbatim}
New identifiers are introduced for omitted fields in record patterns
and for the arguments of the implicit selector functions. We use
nested state monad transformers for generating unique names and for
passing through the type constructor and value type environments. The
former is used to look up the valid constructors of an expression's
type and the latter is augmented with the types of the new variables.
\begin{verbatim}

> type UnlabelState a = StateT ValueEnv (ReaderT TCEnv (StateT Int Id)) a

> run :: UnlabelState a -> TCEnv -> ValueEnv -> a
> run m tcEnv tyEnv = runSt (callRt (callSt m tyEnv) tcEnv) 1

> unlabel :: TCEnv -> ValueEnv -> Module Type -> (Module Type,ValueEnv)
> unlabel tcEnv tyEnv (Module m es is ds) = (Module m es is ds',tyEnv')
>   where (ds',tyEnv') = run (unlabelModule m tyEnv ds) tcEnv tyEnv

> unlabelModule :: ModuleIdent -> ValueEnv -> [TopDecl Type]
>               -> UnlabelState ([TopDecl Type],ValueEnv)
> unlabelModule m tyEnv ds =
>   do
>     dss' <- mapM (unlabelTopDecl m tyEnv) ds
>     tyEnv' <- fetchSt
>     return (concat dss',tyEnv')

\end{verbatim}
At the top-level of a module, we change record constructor
declarations into normal declarations and introduce the implicit
selector function for each field label.

\ToDo{Instantiate quantified type variables in the types of the
  arguments of the selector functions with fresh type variables.}
\begin{verbatim}

> unlabelTopDecl :: ModuleIdent -> ValueEnv -> TopDecl Type
>                -> UnlabelState [TopDecl Type]
> unlabelTopDecl m tyEnv (DataDecl p cx tc tvs cs clss) =
>   do
>     ds' <-
>       mapM (selectorDecl m tyEnv p (map (qualifyWith m . constr) cs))
>            (nub (concatMap labels cs))
>     return (DataDecl p cx tc tvs (map unlabelConstrDecl cs) clss : ds')
>   where unlabelConstrDecl (ConstrDecl p evs cx c tys) =
>           ConstrDecl p evs cx c tys
>         unlabelConstrDecl (RecordDecl p evs cx c fs) =
>           ConstrDecl p evs cx c [ty | FieldDecl _ ls ty <- fs, _ <- ls]
> unlabelTopDecl m tyEnv (NewtypeDecl p cx tc tvs nc clss) =
>   do
>     ds' <- newSelectorDecl m tyEnv p (qualifyWith m (nconstr nc))
>     return (NewtypeDecl p cx tc tvs (unlabelNewConstrDecl nc) clss : ds')
>   where unlabelNewConstrDecl (NewConstrDecl p c ty) = NewConstrDecl p c ty
>         unlabelNewConstrDecl (NewRecordDecl p c _ ty) = NewConstrDecl p c ty
> unlabelTopDecl _ _ (TypeDecl p tc tvs ty) = return [TypeDecl p tc tvs ty]
> unlabelTopDecl m _ (ClassDecl p cx cls tv ds) =
>   liftM (return . ClassDecl p cx cls tv . (tds ++)) (mapM (unlabelDecl m) vds)
>   where (tds,vds) = partition isTypeSig ds
> unlabelTopDecl m _ (InstanceDecl p cx cls ty ds)=
>   liftM (return . InstanceDecl p cx cls ty) (mapM (unlabelDecl m) ds)
> unlabelTopDecl _ _ (DefaultDecl p tys) = return [DefaultDecl p tys]
> unlabelTopDecl m _ (BlockDecl d) =
>   liftM (return . BlockDecl) (unlabelDecl m d)
> unlabelTopDecl _ _ (SplitAnnot p) = return [SplitAnnot p]

> selectorDecl :: ModuleIdent -> ValueEnv -> Position -> [QualIdent] -> Ident
>              -> UnlabelState (TopDecl Type)
> selectorDecl m tyEnv p cs l =
>   liftM (BlockDecl . matchDecl p l . concat) (mapM (selectorEqn m tyEnv l) cs)
>   where matchDecl p f eqs = FunctionDecl p f [funEqn p f [t] e | (t,e) <- eqs]

> selectorEqn :: ModuleIdent -> ValueEnv -> Ident -> QualIdent
>             -> UnlabelState [(ConstrTerm Type,Expression Type)]
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
>                 -> UnlabelState [TopDecl Type]
> newSelectorDecl m tyEnv p c
>   | l /= anonId =
>       do
>         v <- freshVar m "_#rec" (head tys)
>         return [matchDecl p l (constrPattern ty0 c [v]) (uncurry mkVar v)]
>   | otherwise = return []
>   where (l:_,_,ty) = conType c tyEnv
>         (tys,ty0) = arrowUnapply (rawType ty)
>         matchDecl p f t e = BlockDecl (funDecl p f [t] e)

\end{verbatim}
Within block level declarations, the compiler replaces record patterns
and expressions.
\begin{verbatim}

> unlabelDecl :: ModuleIdent -> Decl Type -> UnlabelState (Decl Type)
> unlabelDecl m (FunctionDecl p f eqs) =
>   liftM (FunctionDecl p f) (mapM (unlabelEquation m) eqs)
> unlabelDecl _ (ForeignDecl p cc s ie f ty) =
>   return (ForeignDecl p cc s ie f ty)
> unlabelDecl m (PatternDecl p t rhs) =
>   liftM2 (PatternDecl p) (unlabelTerm m t) (unlabelRhs m rhs)
> unlabelDecl _ (FreeDecl p vs) = return (FreeDecl p vs)

> unlabelEquation :: ModuleIdent -> Equation Type
>                 -> UnlabelState (Equation Type)
> unlabelEquation m (Equation p lhs rhs) =
>   liftM2 (Equation p) (unlabelLhs m lhs) (unlabelRhs m rhs)

\end{verbatim}
Record patterns are transformed into normal constructor patterns by
rearranging fields in the order of the record's declaration, adding
fresh variables in place of omitted fields, and discarding the field
labels.

Note: By rearranging fields here we loose the ability to comply
strictly with the Haskell 98 pattern matching semantics, which matches
fields of a record pattern in the order of their occurrence in the
pattern. However, keep in mind that Haskell matches alternatives from
top to bottom and arguments within an equation or alternative from
left to right, which is not the case in Curry except for rigid case
expressions.
\begin{verbatim}

> unlabelLhs :: ModuleIdent -> Lhs Type -> UnlabelState (Lhs Type)
> unlabelLhs m (FunLhs f ts) = liftM (FunLhs f) (mapM (unlabelTerm m) ts)

> unlabelTerm :: ModuleIdent -> ConstrTerm Type
>             -> UnlabelState (ConstrTerm Type)
> unlabelTerm _ (LiteralPattern ty l) = return (LiteralPattern ty l)
> unlabelTerm _ (VariablePattern ty v) = return (VariablePattern ty v)
> unlabelTerm m (ConstructorPattern ty c ts) =
>   liftM (ConstructorPattern ty c) (mapM (unlabelTerm m) ts)
> unlabelTerm m (RecordPattern ty c fs) =
>   do
>     tcEnv <- liftSt envRt
>     (ls,tys) <- liftM (argumentTypes tcEnv ty c) fetchSt
>     ts <- zipWithM argument tys (orderFields fs ls)
>     unlabelTerm m (ConstructorPattern ty c ts)
>   where argument ty = maybe (fresh ty) return
>         fresh ty = liftM (uncurry VariablePattern) (freshVar m "_#rec" ty)
> unlabelTerm m (AsPattern v t) = liftM (AsPattern v) (unlabelTerm m t)
> unlabelTerm m (LazyPattern t) = liftM LazyPattern (unlabelTerm m t)

\end{verbatim}
Record construction expressions are transformed into normal
constructor applications by rearranging fields in the order of the
record's declaration, passing \texttt{Prelude.undefined} in place of
omitted fields, and discarding the field labels. The transformation of
record update expressions is a bit more involved as we must match the
updated expression with all valid constructors of the expression's
type. As stipulated by the Haskell 98 Report, a record update
expression \texttt{$e$\char`\{\ $l_1$=$e_1$, $\dots$, $l_k$=$e_k$
  \char`\}} succeeds only if $e$ reduces to a value
$C\;e'_1\dots\;e'_n$ such that $C$'s declaration contains \emph{all}
field labels $l_1,\dots,l_k$. In contrast to Haskell we do not report
an error if this is not the case but rather fail only the current
solution.

\ToDo{Reconsider failing with a runtime error.}
\begin{verbatim}

> unlabelRhs :: ModuleIdent -> Rhs Type -> UnlabelState (Rhs Type)
> unlabelRhs m (SimpleRhs p e ds) =
>   do
>     ds' <- mapM (unlabelDecl m) ds
>     e' <- unlabelExpr m p e
>     return (SimpleRhs p e' ds')
> unlabelRhs m (GuardedRhs es ds) =
>   do
>     ds' <- mapM (unlabelDecl m) ds
>     es' <- mapM (unlabelCondExpr m) es
>     return (GuardedRhs es' ds')

> unlabelCondExpr :: ModuleIdent -> CondExpr Type
>                 -> UnlabelState (CondExpr Type)
> unlabelCondExpr m (CondExpr p g e) =
>   liftM2 (CondExpr p) (unlabelExpr m p g) (unlabelExpr m p e)

> unlabelExpr :: ModuleIdent -> Position -> Expression Type
>             -> UnlabelState (Expression Type)
> unlabelExpr _ _ (Literal ty l) = return (Literal ty l)
> unlabelExpr _ _ (Variable ty v) = return (Variable ty v)
> unlabelExpr _ _ (Constructor ty c) = return (Constructor ty c)
> unlabelExpr m p (Record ty c fs) =
>   do
>     tcEnv <- liftSt envRt
>     (ls,tys) <- liftM (argumentTypes tcEnv ty c) fetchSt
>     let es = zipWith argument tys (orderFields fs ls)
>     unlabelExpr m p (applyConstr ty c tys es)
>   where argument ty = maybe (prelFailed ty) id
> unlabelExpr m p (RecordUpdate e fs) =
>   do
>     tyEnv <- fetchSt
>     tcEnv <- liftSt envRt
>     as <-
>       mapM (updateAlt m tcEnv tyEnv . qualifyLike tc) (constructors tc tcEnv)
>     unlabelExpr m p (Fcase e (map (uncurry (caseAlt p)) (concat as)))
>   where ty = typeOf e
>         tc = rootOfType (arrowBase ty)
>         ls = [unqualify l | Field l _ <- fs]
>         updateAlt m tcEnv tyEnv c
>           | all (`elem` ls') ls =
>               do
>                 vs <- mapM (freshVar m "_#rec") tys
>                 let es = zipWith argument vs (orderFields fs ls')
>                 return [(constrPattern ty c vs,applyConstr ty c tys es)]
>           | otherwise = return []
>           where (ls',tys) = argumentTypes tcEnv ty c tyEnv
>         argument v = maybe (uncurry mkVar v) id
> unlabelExpr m p (Apply e1 e2) =
>   liftM2 Apply (unlabelExpr m p e1) (unlabelExpr m p e2)
> unlabelExpr m _ (Lambda p ts e) =
>   liftM2 (Lambda p) (mapM (unlabelTerm m) ts) (unlabelExpr m p e)
> unlabelExpr m p (Let ds e) =
>   liftM2 Let (mapM (unlabelDecl m) ds) (unlabelExpr m p e)
> unlabelExpr m p (Case e as) =
>   liftM2 Case (unlabelExpr m p e) (mapM (unlabelAlt m) as)
> unlabelExpr m p (Fcase e as) =
>   liftM2 Fcase (unlabelExpr m p e) (mapM (unlabelAlt m) as)

> unlabelAlt :: ModuleIdent -> Alt Type -> UnlabelState (Alt Type)
> unlabelAlt m (Alt p t rhs) =
>   liftM2 (Alt p) (unlabelTerm m t) (unlabelRhs m rhs)

\end{verbatim}
Generation of fresh names.
\begin{verbatim}

> freshVar :: ModuleIdent -> String -> Type -> UnlabelState (Type,Ident)
> freshVar m prefix ty =
>   do
>     v <- liftM (mkName prefix) (liftSt (liftRt (updateSt (1 +))))
>     updateSt_ (bindFun m v 0 (monoType ty))
>     return (ty,v)
>   where mkName pre n = mkIdent (pre ++ show n)

\end{verbatim}
Prelude entities.
\begin{verbatim}

> prelFailed :: a -> Expression a
> prelFailed a = Variable a (qualifyWith preludeMIdent (mkIdent "failed"))

\end{verbatim}
Auxiliary definitions.
\begin{verbatim}

> constrPattern :: a -> QualIdent -> [(a,Ident)] -> ConstrTerm a
> constrPattern ty c vs =
>   ConstructorPattern ty c (map (uncurry VariablePattern) vs)

> applyConstr :: Type -> QualIdent -> [Type] -> [Expression Type]
>             -> Expression Type
> applyConstr ty c tys = apply (Constructor (foldr TypeArrow ty tys) c)

\end{verbatim}
