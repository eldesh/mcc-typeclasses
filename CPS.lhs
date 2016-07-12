% -*- LaTeX -*-
% $Id: CPS.lhs 3266 2016-07-12 20:38:47Z wlux $
%
% Copyright (c) 2003-2015, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CPS.lhs}
\section{Continuation Passing Style}\label{sec:cps}
\begin{verbatim}

> module CPS(CPSFunction(..), CPSContinuation(..),
>            CPSFun(..), CPSCont(..), CPSContFun(..),
>            BindC(..), BindPapp(..), CaseBlock(..), CPSTag(..), CPSStmt(..),
>            cpsFunction, cpsApply, cpsInst, continuations) where
> import Cam
> import List
> import Set
> import SCC

\end{verbatim}
In order to implement concurrent threads and encapsulated search in a
portable way, the compiler first transforms every abstract machine
code function into continuation passing style (CPS). Thus, all return
addresses and in particular the addresses where a computation is
resumed after a thread switch and in an encapsulated search,
respectively, correspond to the address of a function in the
transformed code. During the translation, the compiler also adds code
which instantiates unbound variables in flexible switch statements and
implements stability when it is enabled.

Special code is generated for the functions \texttt{@}$_n$. This code
evaluates the first argument of the function and then matches the
arity of the resulting partial application node. If too few arguments
are supplied to the partial application, a new partial application
node is returned, which includes the additional arguments. Otherwise,
the application is entered through its application entry point. If the
closure is applied to too many arguments the application entry point
is entered with the expected number of arguments and the supplied
continuation takes care of applying its result to the remaining
arguments.

An abstract machine code function may be transformed into more than
one CPS function. In order to avoid name conflicts, the compiler
assigns a distinct integer key to each continuation defined in a CPS
function.

A CPS continuation function has two argument lists. The first contains
the proper arguments of the function and the second the free variables
of the function's body. Note that \texttt{CPSChoice} does not allow
passing arguments to its continuations, so these continuations must
not have proper function arguments (cf.\ \texttt{cpsInst} below). The
continuation argument of a continuation function provides the context
in which it is defined and called. At present, we make use of this
feature only to provide a more efficient calling sequence for the code
that instantiates variables in a flexible switch.

A statement \texttt{CPSSwitchArity \char`\{\ gvar:$st_g$; free:$st_l$;
  1:$st_1$; $\dots$ n:$st_n$; \_:$st_{n+1}$ \char`\}} dispatches on
the arity, i.e., the number of missing arguments, of a matched partial
application node. The first two statements $st_g$ and $st_l$ are
selected when a global variable or an unbound logical variable is
matched, respectively. The last statement $st_{n+1}$ is selected if
the arity of the matched node is greater than $n$. This default case
is used to allocate a fresh partial application node combining the
arguments of the matched node and the supplied arguments with a
\texttt{CPSLetPapp} statement.
\begin{verbatim}

> data CPSFunction = CPSFunction Name [Name] CPSStmt deriving Show
> data CPSContinuation =
>   CPSContinuation CPSContFun [Name] [Name] CPSStmt
>   deriving Show
> data CPSStmt =
>     CPSFail
>   | CPSExecCont CPSCont [Name]
>   | CPSExec CPSFun CPSCont [Name]
>   | CPSLet [Bind] CPSStmt
>   | CPSLetC BindC CPSStmt
>   | CPSLetPapp BindPapp CPSStmt
>   | CPSLetCont CPSContinuation CPSStmt
>   | CPSSwitch Bool Name [CaseBlock]
>   | CPSSwitchArity Name [CPSStmt]
>   | CPSChoice (Maybe Name) [CPSCont]
>   deriving Show

> data CPSFun =
>   CPSFun Name | CPSEval Bool Name | CPSUnify | CPSDelay | CPSReadGlobal
>   deriving Show
> data CPSCont = CPSReturn | CPSCont CPSContFun [Name] CPSCont deriving Show
> data CPSContFun =
>     CPSContFun Name Int
>   | CPSApp Int
>   | CPSInst Tag
>   | CPSApply Name
>   | CPSUpdate
>   deriving Show

> data BindC = BindC Name CRetType CCall deriving Show
> data BindPapp = BindPapp Name Name [Name] deriving Show
> data CaseBlock = CaseBlock CPSTag CPSStmt deriving Show
> data CPSTag =
>     CPSLitCase Literal
>   | CPSConstrCase Name [Name]
>   | CPSFreeCase
>   | CPSGlobalCase
>   | CPSDefaultCase
>   deriving Show

> cpsFunction :: Name -> [Name] -> Stmt -> CPSFunction
> cpsFunction f vs st
>   | null ws = CPSFunction f vs st'
>   | otherwise = error ("internal error: cpsFunction " ++ demangle f)
>   where ws = filter (`notElem` vs) (freeVars st CPSReturn)
>         (_,st') = cpsStmt f Nothing (True,CPSReturn) 1 st

> cpsApply :: Name -> [Name] -> CPSContinuation
> cpsApply v vs = CPSContinuation f [v] vs (CPSSwitchArity v cases)
>   where f = CPSApp (length vs)
>         k = CPSCont f vs CPSReturn
>         cases =
>           cpsRigidCase CPSGlobalCase k v : cpsRigidCase CPSFreeCase k v :
>           [CPSExecCont (apply v i vs CPSReturn) [v] | i <- [1..length vs]] ++
>           [CPSLetPapp (BindPapp tmp v vs) (CPSExecCont CPSReturn [tmp])]
>         apply v i vs = CPSCont (CPSApply v) vs' . applyCont vs''
>           where (vs',vs'') = splitAt i vs
>         applyCont vs
>           | null vs = id
>           | otherwise = CPSCont (CPSApp (length vs)) vs

> cpsInst :: Name -> Tag -> CPSContinuation
> cpsInst v t =
>   CPSContinuation (CPSInst t) [] [v] $
>   foldr (CPSLet . return) (CPSExec CPSUnify CPSReturn [v,tmp])
>         (cpsFresh tmp t)

> cpsCont :: CPSContinuation -> CPSCont
> cpsCont (CPSContinuation f _ ws _) = CPSCont f ws CPSReturn

\end{verbatim}
The transformation into CPS code is implemented by a one-pass top-down
algorithm. The abstract machine code statements \texttt{return},
\texttt{eval}, \texttt{exec}, and \texttt{ccall} are transformed
directly into their CPS equivalents. Statement sequences $x$
\texttt{<-} \emph{st$_1$}\texttt{;} \emph{st$_2$}, where \emph{st$_1$}
is neither a \texttt{return} nor a \texttt{ccall} statement, are
transformed by creating a new continuation from \emph{st$_2$}, whose
first input argument is $x$.

The transformation of \texttt{switch} statements is more complicated
because the code of the switch is entered again after an unbound
variable has been instantiated. For that reason, no other code should
precede a transformed \texttt{switch} statement. Furthermore, the
unbound variable cases in transformed \texttt{switch} statements must
know the name of the current function. This is handled by passing on a
continuation for the current function in \texttt{cpsStmt} as long as
no code has been generated. When \texttt{cpsStmt} is about to
transform a \texttt{switch} statement and this continuation is still
available, the statement is transformed with \texttt{cpsSwitch}.
Otherwise \texttt{cpsJumpSwitch} is used, which generates a new
function that performs the switch, and the \texttt{switch} statement is
transformed into a jump to that function.

The translation of a \texttt{choice} statement has to ensure that all
alternatives use the same input variables so that the runtime system
does not need to construct separate closures for each of them.
\begin{verbatim}

> cps :: Name -> (Bool,CPSCont) -> [Name] -> Int -> Stmt
>     -> (Int,CPSContinuation)
> cps f k vs n st = (n',f')
>   where f' = CPSContinuation (CPSContFun f n) vs ws st'
>         ws = filter (`notElem` vs) (freeVars st (snd k))
>         (n',st') = cpsStmt f (Just (cpsCont f')) k (n + 1) st

> cpsCase :: Name -> (Bool,CPSCont) -> Int -> Case -> (Int,CaseBlock)
> cpsCase f k n (Case t st) = (n',CaseBlock (cpsTag t) st')
>   where (n',st') = cpsStmt f Nothing k n st

> cpsTag :: Tag -> CPSTag
> cpsTag (LitCase l) = CPSLitCase l
> cpsTag (ConstrCase c vs) = CPSConstrCase c vs
> cpsTag DefaultCase = CPSDefaultCase

> cpsStmt :: Name -> Maybe CPSCont -> (Bool,CPSCont) -> Int -> Stmt
>         -> (Int,CPSStmt)
> cpsStmt _ _ k n (Return e) =
>   case e of
>     Var v -> (n,CPSExecCont (snd k) [v])
>     _ -> (n,CPSLet [Bind tmp e] (CPSExecCont (snd k) [tmp]))
> cpsStmt _ _ k n (Eval v) = (n,CPSExec (CPSEval (fst k) v) (snd k) [v])
> cpsStmt _ _ k n (Exec f vs) = (n,CPSExec (CPSFun f) (snd k) vs)
> cpsStmt _ _ k n (Apply v vs) =
>   (n,CPSExecCont (CPSCont (CPSApp (length vs)) vs (snd k)) [v])
> cpsStmt _ _ k n (CCall _ ty cc) =
>   (n,CPSLetC (BindC tmp ty cc) (CPSExecCont (snd k) [tmp]))
> cpsStmt f k0 k n (Seq (v :<- st1) st2) =
>   case st1 of
>     Seq st1' st2' -> cpsStmt f k0 k n (Seq st1' (Seq (v :<- st2') st2))
>     Let ds st1' -> cpsStmt f k0 k n (Let ds (Seq (v :<- st1') st2))
>     Return e -> (n',CPSLet [Bind v e] st2')
>       where (n',st2') = cpsStmt f Nothing k n st2
>     CCall _ ty cc -> (n',CPSLetC (BindC v ty cc) st2')
>       where (n',st2') = cpsStmt f Nothing k n st2
>     _ -> (n'',st1')
>       where (n',st1') = cpsStmtSeq f k0 f' n st1
>             (n'',f') = cps f k [v] n' st2
> cpsStmt f _ k n (Let ds st) = (n',foldr CPSLet st' (scc bound free ds))
>   where (n',st') = cpsStmt f Nothing k n st
>         bound (Bind v _) = [v]
>         free (Bind _ n) = exprVars n
> cpsStmt f k0 k n (Switch rf v cases) =
>   maybe (cpsJumpSwitch f) (cpsSwitch f) k0 k n rf v cases
> cpsStmt f k0 k n (Choice alts) =
>   case alts of
>     [] -> (n,CPSFail)
>     [st] -> cpsStmt f k0 k n st
>     _ -> (n',foldr CPSLetCont (CPSChoice Nothing (map cpsCont ks')) ks')
>   where (n',ks) = mapAccumL (cps f k []) n alts
>         ks' = map (updEnv (freeVars (Choice alts) (snd k))) ks
>         updEnv ws (CPSContinuation f vs _ st) = CPSContinuation f vs ws st

> cpsStmtSeq :: Name -> Maybe CPSCont -> CPSContinuation -> Int -> Stmt
>            -> (Int,CPSStmt)
> cpsStmtSeq f k0 (CPSContinuation _ vs _ (CPSExecCont k vs')) n st
>   | vs == vs' = cpsStmt f k0 (tagged k,k) n st
>   where tagged CPSReturn = True
>         tagged (CPSCont f _ _) = taggedCont f
>         taggedCont (CPSContFun _ _) = True
>         taggedCont (CPSApp _) = False
>         taggedCont (CPSInst t) = taggedSwitch [t]
>         taggedCont (CPSApply _) = False
>         taggedCont CPSUpdate = True
> cpsStmtSeq f k0 f' n st = (n',CPSLetCont f' st')
>   where (n',st') = cpsStmt f k0 (tagged f',cpsCont f') n st
>         tagged (CPSContinuation _ vs _ (CPSSwitch tagged v _)) =
>           vs /= [v] || tagged
>         tagged (CPSContinuation _ vs _ (CPSSwitchArity v _)) = vs /= [v]
>         tagged _ = True

> cpsJumpSwitch :: Name -> (Bool,CPSCont) -> Int -> RF -> Name -> [Case]
>               -> (Int,CPSStmt)
> cpsJumpSwitch f k n rf v cases = (n',CPSLetCont f' (CPSExecCont k' [v]))
>   where f' = CPSContinuation (CPSContFun f n) [v] ws st'
>         k' = cpsCont f'
>         ws = filter (v /=) (freeVars (Switch rf v cases) (snd k))
>         (n',st') = cpsSwitch f k' k (n + 1) rf v cases

> cpsSwitch :: Name -> CPSCont -> (Bool,CPSCont) -> Int -> RF -> Name -> [Case]
>           -> (Int,CPSStmt)
> cpsSwitch f k0 k n rf v cases =
>   (n',CPSSwitch tagged v (gcase ++ vcase ++ cases'))
>   where gcase = map (CaseBlock CPSGlobalCase) (cpsGlobalCase rf k0 v ts)
>         vcase = map (CaseBlock CPSFreeCase) (cpsVarCase rf k0 v ts)
>         (n',cases') = mapAccumL (cpsCase f k) n cases
>         ts = [t | Case t _ <- cases, t /= DefaultCase]
>         tagged = taggedSwitch ts

> cpsGlobalCase :: RF -> CPSCont -> Name -> [Tag] -> [CPSStmt]
> cpsGlobalCase Rigid k v _ = [cpsRigidCase CPSGlobalCase k v]
> cpsGlobalCase Flex k v ts = [cpsRigidCase CPSGlobalCase k v | not (null ts)]

> cpsVarCase :: RF -> CPSCont -> Name -> [Tag] -> [CPSStmt]
> cpsVarCase Rigid k v _ = [cpsRigidCase CPSFreeCase k v]
> cpsVarCase Flex k v ts = [cpsFlexCase k v ts | not (null ts)]

> cpsRigidCase :: CPSTag -> CPSCont -> Name -> CPSStmt
> cpsRigidCase CPSGlobalCase k v = CPSExec CPSReadGlobal k [v]
> cpsRigidCase CPSFreeCase k v = CPSExec CPSDelay k [v]

> cpsFlexCase :: CPSCont -> Name -> [Tag] -> CPSStmt
> cpsFlexCase k v ts = cpsFlexChoice v [CPSCont (CPSInst t) [v] k | t <- ts]

> cpsFlexChoice :: Name -> [CPSCont] -> CPSStmt
> cpsFlexChoice _ [k] = CPSExecCont k []
> cpsFlexChoice v ks = CPSChoice (Just v) ks

> cpsFresh :: Name -> Tag -> [Bind]
> cpsFresh v (LitCase l) = [Bind v (Lit l)]
> cpsFresh v (ConstrCase c vs) =
>   [Bind v Free | v <- vs] ++ [Bind v (Constr c vs)]

> taggedSwitch :: [Tag] -> Bool
> taggedSwitch = foldr tagged True
>   where tagged (LitCase (Char _)) _ = True
>         tagged (LitCase (Int _)) _ = True
>         tagged (LitCase (Integer _)) _ = True
>         tagged (LitCase (Float _)) _ = False
>         tagged (ConstrCase _ _) _ = False
>         tagged DefaultCase t = t

> freeVars :: Stmt -> CPSCont -> [Name]
> freeVars st k = nub (stmtVars st (contVars k))

> contVars :: CPSCont -> [Name]
> contVars CPSReturn = []
> contVars (CPSCont f ws k) = contFunVars f ++ ws ++ contVars k

> contFunVars :: CPSContFun -> [Name]
> contFunVars (CPSContFun _ _) = []
> contFunVars (CPSApp _) = []
> contFunVars (CPSInst _) = []
> contFunVars (CPSApply v) = [v]
> contFunVars CPSUpdate = []

> stmtVars :: Stmt -> [Name] -> [Name]
> stmtVars (Return e) vs = exprVars e ++ vs
> stmtVars (Eval v) vs = v : vs
> stmtVars (Exec _ vs) vs' = vs ++ vs'
> stmtVars (Apply v vs) vs' = v : vs ++ vs'
> stmtVars (CCall _ _ cc) vs = ccallVars cc ++ vs
> stmtVars (Seq (v :<- st1) st2) vs =
>   stmtVars st1 [] ++ filter (v /=) (stmtVars st2 vs)
> stmtVars (Let ds st) vs = filter (`notElemSet` bvs) (fvs ++ stmtVars st vs)
>   where bvs = fromListSet [v | Bind v _ <- ds]
>         fvs = concat [exprVars n | Bind _ n <- ds]
> stmtVars (Switch _ v cases) vs = v : concatMap caseVars cases ++ vs
> stmtVars (Choice alts) vs = concatMap (flip stmtVars []) alts ++ vs

> caseVars :: Case -> [Name]
> caseVars (Case t st) =
>   filter (`notElemSet` fromListSet (tagVars t)) (stmtVars st [])

> ccallVars :: CCall -> [Name]
> ccallVars (StaticCall _ xs) = map snd xs
> ccallVars (DynamicCall v xs) = v : map snd xs
> ccallVars (StaticAddr _) = []

> exprVars :: Expr -> [Name]
> exprVars (Lit _) = []
> exprVars (Constr _ vs) = vs
> exprVars (Papp _ vs) = vs
> exprVars (Closure _ vs) = vs
> exprVars (Lazy _ vs) = vs
> exprVars Free = []
> exprVars (Var v) = [v]

> tagVars :: Tag -> [Name]
> tagVars (LitCase _) = []
> tagVars (ConstrCase _ vs) = vs
> tagVars DefaultCase = []

> tmp :: Name
> tmp = Name "_"

\end{verbatim}
The function \texttt{continuations} returns all local continuation
functions defined in a transformed function.
\begin{verbatim}

> continuations :: CPSFunction -> [CPSContinuation]
> continuations (CPSFunction _ _ st) = contsStmt st

> contsCont :: CPSContinuation -> [CPSContinuation]
> contsCont (CPSContinuation _ _ _ st) = contsStmt st

> contsStmt :: CPSStmt -> [CPSContinuation]
> contsStmt CPSFail = []
> contsStmt (CPSExecCont _ _) = []
> contsStmt (CPSExec _ _ _) = []
> contsStmt (CPSLet _ st) = contsStmt st
> contsStmt (CPSLetC _ st) = contsStmt st
> contsStmt (CPSLetPapp _ st) = contsStmt st
> contsStmt (CPSLetCont k st) = k : contsCont k ++ contsStmt st
> contsStmt (CPSSwitch _ _ cases) =
>   concat [contsStmt st | CaseBlock _ st <- cases]
> contsStmt (CPSSwitchArity _ sts) = concatMap contsStmt sts
> contsStmt (CPSChoice _ _) = []

\end{verbatim}
