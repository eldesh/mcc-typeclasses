% -*- LaTeX -*-
% $Id: CPS.lhs 2997 2010-08-30 19:16:14Z wlux $
%
% Copyright (c) 2003-2009, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CPS.lhs}
\section{Continuation Passing Style}\label{sec:cps}
\begin{verbatim}

> module CPS(CPSFunction(..), CPSContinuation(..),
>            CPSFun(..), CPSPrim(..), CPSCont(..),
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
not have proper function arguments (cf. \texttt{cpsInst} below). The
continuation argument of a continuation function provides the context
in which it is defined and called. At present, we make use of this
feature only to provide a more efficient calling sequence for the code
that instantiates variables in a flexible switch.

The idiosyncratic \texttt{CPSSwitchVar} statement allows
distinguishing local and global unbound logical variables of a search
goal within an encapsulated search. The first alternative is chosen
for a global unbound variable, which must not be instantiated, and the
second is chosen for a local unbound variable, which can be
instantiated.

A statement \texttt{CPSSwitchArity \char`\{\ 0:$st_0$; \dots;
  n:$st_n$; \_:$st_{n+1}$ \char`\}} dispatches on the arity, i.e., the
number of missing arguments, of a matched partial application node.
The first statement $st_0$, corresponding to arity 0, is selected when
an unbound logical variable is matched, and the last statement
$st_{n+1}$ is selected if the arity of the matched node is greater
than $n$. This default case will allocate a fresh partial application
node combining the arguments of the matched node and the supplied
arguments with a \texttt{CPSLetPapp} statement.
\begin{verbatim}

> data CPSFunction = CPSFunction Name [Name] CPSStmt deriving Show
> data CPSContinuation =
>   CPSContinuation Name Int [Name] [Name] CPSStmt
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
>   | CPSSwitchVar Name CPSStmt CPSStmt
>   | CPSSwitchArity Name [CPSStmt]
>   | CPSChoice (Maybe Name) [CPSCont]
>   deriving Show

> data CPSFun = CPSFun Name | CPSPrim CPSPrim deriving Show
> data CPSPrim = CPSEval Bool Name | CPSUnify | CPSDelay deriving Show
> data CPSCont =
>     CPSReturn
>   | CPSCont Name Int [Name] CPSCont
>   | CPSInst Name Tag CPSCont
>   | CPSApply Name [Name] CPSCont
>   deriving Show

> data BindC = BindC Name CRetType CCall deriving Show
> data BindPapp = BindPapp Name Name [Name] deriving Show
> data CaseBlock = CaseBlock CPSTag CPSStmt deriving Show
> data CPSTag =
>     CPSLitCase Literal
>   | CPSConstrCase Name [Name]
>   | CPSFreeCase
>   | CPSDefaultCase
>   deriving Show

> cpsFunction :: Name -> [Name] -> Stmt -> CPSFunction
> cpsFunction f vs st
>   | null ws = CPSFunction f vs st'
>   | otherwise = error ("internal error: cpsFunction " ++ demangle f)
>   where ws = filter (`notElem` vs) (freeVars st CPSReturn)
>         (_,st') = cpsStmt f Nothing (True,CPSReturn) 1 st

> cpsApply :: Name -> [Name] -> CPSFunction
> cpsApply f (v:vs) =
>   CPSFunction f (v:vs) $
>   CPSLetCont f' (CPSExec (CPSPrim (CPSEval False v)) k' [v])
>   where f' = CPSContinuation f 1 [v] vs (CPSSwitchArity v cases)
>         k' = cpsCont f'
>         cases =
>           cpsRigidCase k' v :
>           [CPSExecCont (apply v i vs CPSReturn) [v] | i <- [1..length vs]] ++
>           [CPSLetPapp (BindPapp tmp v vs) (CPSExecCont CPSReturn [tmp])]
>         apply v i vs = CPSApply v vs' . applyCont vs''
>           where (vs',vs'') = splitAt i vs
>         applyCont vs
>           | null vs = id
>           | otherwise = CPSCont (apName (length vs)) 1 vs
>         apName n = mangle ('@' : if n == 1 then "" else show n)

> cpsInst :: Name -> Name -> Tag -> CPSContinuation
> cpsInst f v t =
>   CPSContinuation f 0 [] [v] $
>   foldr (CPSLet . return) (CPSExec (CPSPrim CPSUnify) CPSReturn [v,tmp])
>         (cpsFresh tmp t)

> cpsCont :: CPSContinuation -> CPSCont
> cpsCont (CPSContinuation f n _ ws _) = CPSCont f n ws CPSReturn

\end{verbatim}
The transformation into CPS code is implemented by a top-down
algorithm. The abstract machine code statements \texttt{return},
\texttt{enter}, \texttt{exec}, and \texttt{ccall} are transformed
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

The translation of a \texttt{choices} statement has to ensure that all
alternatives use the same input variables so that the runtime system
does not need to construct separate closures for each of them.
\begin{verbatim}

> cps :: Name -> (Bool,CPSCont) -> [Name] -> Int -> Stmt
>     -> (Int,CPSContinuation)
> cps f k vs n st = (n',f')
>   where f' = CPSContinuation f n vs ws st'
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
> cpsStmt _ _ k n (Enter v) =
>   (n,CPSExec (CPSPrim (CPSEval (fst k) v)) (snd k) [v])
> cpsStmt _ _ k n (Exec f vs) = (n,CPSExec (CPSFun f) (snd k) vs)
> cpsStmt _ _ k n (CCall _ ty cc) =
>   (n,CPSLetC (BindC tmp ty cc) (CPSExecCont (snd k) [tmp]))
> cpsStmt f k0 k n (Seq st1 st2) =
>   case st1 of
>     v :<- Seq st1' st2' -> cpsStmt f k0 k n (Seq st1' (Seq (v :<- st2') st2))
>     v :<- Return e -> (n',CPSLet [Bind v e] st2')
>       where (n',st2') = cpsStmt f Nothing k n st2
>     v :<- CCall _ ty cc -> (n',CPSLetC (BindC v ty cc) st2')
>       where (n',st2') = cpsStmt f Nothing k n st2
>     v :<- st -> (n'',CPSLetCont f' st1')
>       where (n',st1') = cpsStmt f k0 (tagged f',cpsCont f') n st
>             (n'',f') = cps f k [v] n' st2
>             tagged (CPSContinuation _ _ vs _ (CPSSwitch tagged v _)) =
>               vs /= [v] || tagged
>             tagged (CPSContinuation _ _ vs _ (CPSSwitchArity v _)) = vs /= [v]
>             tagged _ = True
>     Let ds -> (n',foldr CPSLet st2' (scc bound free ds))
>       where (n',st2') = cpsStmt f Nothing k n st2
>             bound (Bind v _) = [v]
>             free (Bind _ n) = exprVars n
> cpsStmt f k0 k n (Switch rf v cases) =
>   maybe (cpsJumpSwitch f) (cpsSwitch f) k0 k n rf v cases
> cpsStmt f k0 k n (Choices alts) =
>   case alts of
>     [] -> (n,CPSFail)
>     [st] -> cpsStmt f k0 k n st
>     _ -> (n',foldr CPSLetCont (CPSChoice Nothing (map cpsCont ks')) ks')
>   where (n',ks) = mapAccumL (cps f k []) n alts
>         ks' = map (updEnv (freeVars (Choices alts) (snd k))) ks
>         updEnv ws (CPSContinuation f n vs _ st) = CPSContinuation f n vs ws st

> cpsJumpSwitch :: Name -> (Bool,CPSCont) -> Int -> RF -> Name -> [Case]
>               -> (Int,CPSStmt)
> cpsJumpSwitch f k n rf v cases = (n',CPSLetCont f' (CPSExecCont k' [v]))
>   where f' = CPSContinuation f n [v] ws st'
>         k' = cpsCont f'
>         ws = filter (v /=) (freeVars (Switch rf v cases) (snd k))
>         (n',st') = cpsSwitch f k' k (n + 1) rf v cases

> cpsSwitch :: Name -> CPSCont -> (Bool,CPSCont) -> Int -> RF -> Name -> [Case]
>           -> (Int,CPSStmt)
> cpsSwitch f k0 k n rf v cases = (n',CPSSwitch tagged v (vcase ++ cases'))
>   where vcase = map (CaseBlock CPSFreeCase) (cpsVarCase rf k0 v ts)
>         (n',cases') = mapAccumL (cpsCase f k) n cases
>         ts = [t | Case t _ <- cases, t /= DefaultCase]
>         tagged = taggedSwitch ts

> cpsVarCase :: RF -> CPSCont -> Name -> [Tag] -> [CPSStmt]
> cpsVarCase Rigid k v _ = [cpsRigidCase k v]
> cpsVarCase Flex k v ts =
>   [CPSSwitchVar v (cpsRigidCase k v) (cpsFlexCase k v ts) | not (null ts)]

> cpsRigidCase :: CPSCont -> Name -> CPSStmt
> cpsRigidCase k v = CPSExec (CPSPrim CPSDelay) k [v]

> cpsFlexCase :: CPSCont -> Name -> [Tag] -> CPSStmt
> cpsFlexCase k v ts = cpsFlexChoice v [CPSInst v t k | t <- ts]

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
> contVars (CPSCont _ _ ws k) = ws ++ contVars k
> contVars (CPSInst v _ k) = v : contVars k
> contVars (CPSApply v vs k) = v : vs ++ contVars k

> stmtVars :: Stmt -> [Name] -> [Name]
> stmtVars (Return e) vs = exprVars e ++ vs
> stmtVars (Enter v) vs = v : vs
> stmtVars (Exec _ vs) vs' = vs ++ vs'
> stmtVars (CCall _ _ cc) vs = ccallVars cc ++ vs
> stmtVars (Seq st1 st2) vs = stmt0Vars st1 (stmtVars st2 vs)
> stmtVars (Switch _ v cases) vs = v : concatMap caseVars cases ++ vs
> stmtVars (Choices alts) vs = concatMap (flip stmtVars []) alts ++ vs

> stmt0Vars :: Stmt0 -> [Name] -> [Name]
> stmt0Vars (v :<- st) vs = stmtVars st (filter (v /=) vs)
> stmt0Vars (Let ds) vs = filter (`notElemSet` bvs) (fvs ++ vs)
>   where bvs = fromListSet [v | Bind v _ <- ds]
>         fvs = concat [exprVars n | Bind _ n <- ds]

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
> contsCont (CPSContinuation _ _ _ _ st) = contsStmt st

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
> contsStmt (CPSSwitchVar _ st1 st2) = contsStmt st1 ++ contsStmt st2
> contsStmt (CPSSwitchArity _ sts) = concatMap contsStmt sts
> contsStmt (CPSChoice _ _) = []

\end{verbatim}
