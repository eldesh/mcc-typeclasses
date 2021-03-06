% -*- LaTeX -*-
% $Id: Lift.lhs 2971 2010-07-01 09:44:53Z wlux $
%
% Copyright (c) 2001-2010, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Lift.lhs}
\section{Lifting Declarations}
After desugaring and simplifying the code, the compiler lifts all
local function declarations to the top-level keeping only local
variable declarations. The algorithm used here is similar to
Johnsson's~\cite{Johnsson87:Thesis} (see also chapter 6
of~\cite{PeytonJonesLester92:Book}). It consists of two phases, first
we abstract each local function declaration, adding its free variables
as initial parameters and update all calls to take these variables
into account. Then all local function declarations are collected and
lifted to the top-level.
\begin{verbatim}

> module Lift(lift) where
> import Base
> import Combined
> import Curry
> import CurryUtils
> import Env
> import List
> import Monad
> import PredefIdent
> import SCC
> import Set
> import Subst
> import TopEnv
> import TrustInfo
> import Types
> import TypeSubst
> import Typing
> import Utils
> import ValueInfo

> lift :: ValueEnv -> TrustEnv -> Module Type -> (ValueEnv,TrustEnv,Module Type)
> lift tyEnv trEnv (Module m es is ds) =
>   (tyEnv',trEnv',Module m es is (concatMap liftTopDecl ds'))
>   where (tyEnv',trEnv',ds') = runSt (callSt (abstractModule m ds) tyEnv) trEnv

\end{verbatim}
\paragraph{Abstraction}
Besides adding the free variables to every (local) function, the
abstraction pass also has to update the type environment in order to
reflect the new types of the abstracted functions. Furthermore,
functions are renamed during abstraction by adding the name of their
enclosing function as prefix to their name. This is done in order to
disambiguate local function names in debugging sessions, but means
that the trust annotation environment must be updated, too. As usual
we use nested state monad transformers in order to pass the
environments through. The abstraction phase also uses a local
environment that maps each local function declaration onto its
replacement expression, i.e. the function applied to its free
variables.
\begin{verbatim}

> type AbstractState a = StateT ValueEnv (StateT TrustEnv Id) a
> type AbstractEnv = Env Ident (Expression Type)

> abstractModule :: ModuleIdent -> [TopDecl Type]
>                -> AbstractState (ValueEnv,TrustEnv,[TopDecl Type])
> abstractModule m ds =
>   do
>     ds' <- mapM (abstractTopDecl m) ds
>     tyEnv' <- fetchSt
>     trEnv' <- liftSt fetchSt
>     return (tyEnv',trEnv',ds')

> abstractTopDecl :: ModuleIdent -> TopDecl Type -> AbstractState (TopDecl Type)
> abstractTopDecl m (BlockDecl d) =
>   liftM BlockDecl (abstractDecl m "" [] emptyEnv d)
> abstractTopDecl _ d = return d

> abstractDecl :: ModuleIdent -> String -> [(Type,Ident)] -> AbstractEnv
>              -> Decl Type -> AbstractState (Decl Type)
> abstractDecl m _ lvs env (FunctionDecl p ty f eqs) =
>   liftM (FunctionDecl p ty f) (mapM (abstractEquation m lvs env) eqs)
> abstractDecl m pre lvs env (PatternDecl p t rhs) =
>   liftM (PatternDecl p t) (abstractRhs m pre lvs env rhs)
> abstractDecl _ _ _ _ d = return d

> abstractEquation :: ModuleIdent -> [(Type,Ident)] -> AbstractEnv
>                  -> Equation Type -> AbstractState (Equation Type)
> abstractEquation m lvs env (Equation p lhs@(FunLhs f ts) rhs) =
>   liftM (Equation p lhs) (abstractRhs m (name f ++ ".") lvs' env rhs)
>   where lvs' = lvs `addVars` concatMap termVars ts

> abstractRhs :: ModuleIdent -> String -> [(Type,Ident)] -> AbstractEnv
>             -> Rhs Type -> AbstractState (Rhs Type)
> abstractRhs m pre lvs env (SimpleRhs p e _) =
>   liftM (flip (SimpleRhs p) []) (abstractExpr m pre lvs env e)

\end{verbatim}
Within a declaration group we have to split the list of declarations
into the function and value declarations. Only the function
declarations are affected by the abstraction algorithm; the value
declarations are left unchanged except for abstracting their right
hand sides.

The abstraction of a recursive declaration group is complicated by the
fact that not all functions need to call each other in a recursive
declaration group. E.g., in the following example neither g nor h
call each other.
\begin{verbatim}
  f = g True
    where x = f 1
          f z = y + z
          y = g False
          g z = if z then x else 0
\end{verbatim}
Because of this fact, f and g can be abstracted separately by adding
only \texttt{y} to \texttt{f} and \texttt{x} to \texttt{g}. On the
other hand, in the following example
\begin{verbatim}
  f x y = g 4
    where g p = h p + x
          h q = k + y + q
          k = g x
\end{verbatim}
the local function \texttt{g} uses \texttt{h}, so the free variables
of \texttt{h} have to be added to \texttt{g} as well. However, because
\texttt{h} does not call \texttt{g} it is sufficient to add only
\texttt{k} and \texttt{y} (and not \texttt{x}) to its definition. We
handle this by computing the dependency graph between the functions
and splitting this graph into its strongly connected components. Each
component is then processed separately, adding the free variables in
the group to its functions.

We have to be careful with local declarations within desugared case
expressions. If some of the cases have guards, e.g.,
\begin{verbatim}
  case e of
    x | x < 1 -> 1
    x -> let double y = y * y in double x
\end{verbatim}
the desugarer at present may duplicate code. While there is no problem
with local variable declarations being duplicated, we must avoid
lifting a local function declaration more than once. Therefore,
\texttt{abstractFunDecls} transforms only those function declarations
that have not been lifted and discards all other declarations. Note
that it is easy to check whether a function has been lifted by
checking whether an entry for its untransformed name is still present
in the type environment.
\begin{verbatim}

> abstractDeclGroup :: ModuleIdent -> String -> [(Type,Ident)] -> AbstractEnv
>                   -> [Decl Type] -> Expression Type
>                   -> AbstractState (Expression Type)
> abstractDeclGroup m pre lvs env ds e =
>   abstractFunDecls m pre lvs' env (scc bv (qfv m) fds) vds e
>   where (fds,vds) = partition isFunDecl ds
>         lvs' = lvs `addVars` concatMap declVars vds

> abstractFunDecls :: ModuleIdent -> String -> [(Type,Ident)] -> AbstractEnv
>                  -> [[Decl Type]] -> [Decl Type] -> Expression Type
>                  -> AbstractState (Expression Type)
> abstractFunDecls m pre lvs env [] vds e =
>   do
>     vds' <- mapM (abstractDecl m pre lvs env) vds
>     e' <- abstractExpr m pre lvs env e
>     return (Let vds' e')
> abstractFunDecls m pre lvs env (fds:fdss) vds e =
>   do
>     tyEnv <- fetchSt
>     let fs' = filter (not . isLifted tyEnv pre) fs
>         fds' = [d | d <- fds, any (`elem` fs') (bv d)]
>         env' = foldr (bindF (map (uncurry mkVar) fvs)) env fs
>     fds'' <-
>       mapM (abstractFunDecl m pre fvs) fds' >>=
>       mapM (abstractDecl m pre lvs env')
>     e' <- abstractFunDecls m pre lvs env' fdss vds e
>     return (Let fds'' e')
>   where fs = bv fds
>         fvs = filter ((`elemSet` fvsRhs) . snd) lvs
>         fvsRhs = fromListSet $
>           concat [maybe [v] (qfv m) (lookupEnv v env) | v <- qfv m fds]
>         bindF fvs f = bindEnv f (apply (mkFun m pre undefined f) fvs)
>         isLifted tyEnv pre f =
>           not (null (lookupTopEnv (liftIdent pre f) tyEnv))

\end{verbatim}
When the free variables of a function are abstracted, the type of the
function must be changed as well. Given a function $f$ with type
$\forall\overline{\alpha} . \tau$ and free variables $x_1, \dots, x_n$
with types $\tau'_1, \dots, \tau'_n$, the type of $f$ after
abstraction will be $\forall\overline{\alpha'} . \tau'_1 \rightarrow
\dots \rightarrow \tau'_n \rightarrow \tau$ where $\overline{\alpha'}
= \emph{vars}(\tau'_1) \cup \dots \cup \emph{vars}(\tau'_n) \cup
\emph{vars}(\tau)$. Since local variables must have monomorphic types,
we do not need to rename $\tau$'s universally quantified type
variables in order to avoid an inadvertent name capturing.
\begin{verbatim}

> abstractFunDecl :: ModuleIdent -> String -> [(Type,Ident)] -> Decl Type
>                 -> AbstractState (Decl Type)
> abstractFunDecl m pre fvs (FunctionDecl p ty f eqs) =
>   do
>     updateSt_ (globalBindFun m f' (eqnArity (head eqs')) (polyType ty'))
>     liftSt (updateSt_ (abstractFunAnnot pre f))
>     return (FunctionDecl p ty' f' eqs')
>   where f' = liftIdent pre f
>         ty' = genType (foldr (TypeArrow . fst) ty fvs)
>         eqs' = map (addVars f') eqs
>         addVars f (Equation p (FunLhs _ ts) rhs) =
>           Equation p (FunLhs f (map (uncurry VariablePattern) fvs ++ ts)) rhs
>         genType ty = subst (foldr2 bindSubst idSubst tvs tvs') ty
>           where tvs = nub (typeVars ty)
>                 tvs' = map TypeVariable [0..]
> abstractFunDecl m pre _ (ForeignDecl p fi ty f ty') =
>   do
>     updateSt_ (globalBindFun m f' (foreignArity ty) (polyType ty))
>     liftSt (updateSt_ (abstractFunAnnot pre f))
>     return (ForeignDecl p fi ty f' ty')
>   where f' = liftIdent pre f

> abstractFunAnnot :: String -> Ident -> Env Ident a -> Env Ident a
> abstractFunAnnot pre f env =
>   case lookupEnv f env of
>     Just ev -> bindEnv (liftIdent pre f) ev (unbindEnv f env)
>     Nothing -> env

> abstractExpr :: ModuleIdent -> String -> [(Type,Ident)] -> AbstractEnv
>              -> Expression Type -> AbstractState (Expression Type)
> abstractExpr _ _ _ _ (Literal ty l) = return (Literal ty l)
> abstractExpr m pre lvs env (Variable ty v)
>   | isQualified v = return (Variable ty v)
>   | otherwise =
>       maybe (return (Variable ty v)) (abstractExpr m pre lvs env . absType ty)
>             (lookupEnv (unqualify v) env)
>   where absType ty (Variable _ v) = Variable ty v
>         absType ty (Apply e1 e2) =
>           Apply (absType (typeOf e2 `TypeArrow` ty) e1) e2
>         absType _ _ = internalError "absType"
> abstractExpr _ _ _ _ (Constructor ty c) = return (Constructor ty c)
> abstractExpr m pre lvs env (Apply e1 e2) =
>   do
>     e1' <- abstractExpr m pre lvs env e1
>     e2' <- abstractExpr m pre lvs env e2
>     return (Apply e1' e2')
> abstractExpr m pre lvs env (Lambda p ts e) =
>   abstractDeclGroup m pre lvs env [funDecl p ty f ts e] (mkVar ty f)
>   where f = lambdaId p
>         ty = typeOf (Lambda p ts e)
> abstractExpr m pre lvs env (Let ds e) = abstractDeclGroup m pre lvs env ds e
> abstractExpr m pre lvs env (Case e alts) =
>   do
>     e' <- abstractExpr m pre lvs env e
>     alts' <- mapM (abstractAlt m pre lvs env) alts
>     return (Case e' alts')
> abstractExpr m pre lvs env (Fcase e alts) =
>   do
>     e' <- abstractExpr m pre lvs env e
>     alts' <- mapM (abstractAlt m pre lvs env) alts
>     return (Fcase e' alts')

> abstractAlt :: ModuleIdent -> String -> [(Type,Ident)] -> AbstractEnv
>             -> Alt Type -> AbstractState (Alt Type)
> abstractAlt m pre lvs env (Alt p t rhs) =
>   liftM (Alt p t) (abstractRhs m pre lvs' env rhs)
>   where lvs' = lvs `addVars` termVars t

\end{verbatim}
\paragraph{Lifting}
After the abstraction pass, all local function declarations are lifted
to the top-level.
\begin{verbatim}

> liftTopDecl :: TopDecl a -> [TopDecl a]
> liftTopDecl (BlockDecl d) = map BlockDecl (liftFunDecl d)
> liftTopDecl d = [d]

> liftFunDecl :: Decl a -> [Decl a]
> liftFunDecl (FunctionDecl p ty f eqs) =
>   (FunctionDecl p ty f eqs' : concat dss')
>   where (eqs',dss') = unzip (map liftEquation eqs)
> liftFunDecl d = [d]

> liftVarDecl :: Decl a -> (Decl a,[Decl a])
> liftVarDecl (PatternDecl p t rhs) = (PatternDecl p t rhs',ds')
>   where (rhs',ds') = liftRhs rhs
> liftVarDecl (FreeDecl p vs) = (FreeDecl p vs,[])

> liftEquation :: Equation a -> (Equation a,[Decl a])
> liftEquation (Equation p lhs rhs) = (Equation p lhs rhs',ds')
>   where (rhs',ds') = liftRhs rhs

> liftRhs :: Rhs a -> (Rhs a,[Decl a])
> liftRhs (SimpleRhs p e _) = (SimpleRhs p e' [],ds')
>   where (e',ds') = liftExpr e

> liftDeclGroup :: [Decl a] -> ([Decl a],[Decl a])
> liftDeclGroup ds = (vds',concat (map liftFunDecl fds ++ dss'))
>   where (fds,vds) = partition isFunDecl ds
>         (vds',dss') = unzip (map liftVarDecl vds)

> liftExpr :: Expression a -> (Expression a,[Decl a])
> liftExpr (Literal a l) = (Literal a l,[])
> liftExpr (Variable a v) = (Variable a v,[])
> liftExpr (Constructor a c) = (Constructor a c,[])
> liftExpr (Apply e1 e2) = (Apply e1' e2',ds' ++ ds'')
>   where (e1',ds') = liftExpr e1
>         (e2',ds'') = liftExpr e2
> liftExpr (Let ds e) = (mkLet ds' e',ds'' ++ ds''')
>   where (ds',ds'') = liftDeclGroup ds
>         (e',ds''') = liftExpr e
> liftExpr (Case e alts) = (Case e' alts',concat (ds':dss'))
>   where (e',ds') = liftExpr e
>         (alts',dss') = unzip (map liftAlt alts)
> liftExpr (Fcase e alts) = (Fcase e' alts',concat (ds':dss'))
>   where (e',ds') = liftExpr e
>         (alts',dss') = unzip (map liftAlt alts)

> liftAlt :: Alt a -> (Alt a,[Decl a])
> liftAlt (Alt p t rhs) = (Alt p t rhs',ds')
>   where (rhs',ds') = liftRhs rhs

\end{verbatim}
\paragraph{Auxiliary definitions}
\begin{verbatim}

> mkFun :: ModuleIdent -> String -> a -> Ident -> Expression a
> mkFun m pre ty f = Variable ty (qualifyWith m (liftIdent pre f))

> globalBindFun :: ModuleIdent -> Ident -> Int -> TypeScheme
>               -> ValueEnv -> ValueEnv
> globalBindFun m f n ty = globalBindTopEnv m f (Value (qualifyWith m f) n ty)

> liftIdent :: String -> Ident -> Ident
> liftIdent prefix x = renameIdent (mkIdent (prefix ++ name x)) (uniqueId x)

> addVars :: [(a,Ident)] -> [(Ident,b,a)] -> [(a,Ident)]
> addVars vs lvs = vs ++ [(ty,v) | (v,_,ty) <- lvs, v `notElem` vs']
>   where vs' = map snd vs

\end{verbatim}
