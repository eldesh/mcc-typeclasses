% -*- LaTeX -*-
% $Id: MachInterp.lhs 3004 2010-08-30 19:44:01Z wlux $
%
% Copyright (c) 1998-2009, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{MachInterp.lhs}
\section{An Interpreter for the Abstract Machine}
This section describes an interpreter for the abstract machine code in
Haskell.
\input{MachTypes.lhs} % \subsection{Basic Types}
\subsection{The Interpreter State Transformers}
For every abstract machine instruction, we implement a corresponding
interpreter function. All these function are based on a kind of
``micro-code'' state transformer.
\begin{verbatim}

> module MachInterp where
> import MachTypes
> import MachNode
> import MachStack
> import MachEnviron
> import MachChoice
> import MachSpace
> import MachThreads
> import MachResult
> import Char
> import Env
> import Monad
> import Combined
> import IO

\end{verbatim}
\subsubsection{Creating Nodes}
A \texttt{return} statement returns a fresh node to the calling
context.
\begin{verbatim}

> returnNode :: (NodePtr -> MachStateT ()) -> Instruction
> returnNode init =
>   do
>     ptr <- read'updateState (allocNode (error "Uninitialized result"))
>     init ptr
>     retNode ptr

> retNode :: NodePtr -> Instruction
> retNode ptr = updateState (pushNode ptr) >> ret

\end{verbatim}
A \texttt{let} statement allocates and initializes a group of nodes.
In order to handle mutually recursive nodes, allocation and
initialization of nodes are separated.
\begin{verbatim}

> letNodes :: [(String,NodePtr -> MachStateT ())] -> Instruction -> Instruction
> letNodes allocs next =
>   do
>     ptrs <- read'updateState (allocNodes (map uninitialized vs))
>     updateState (setVars vs ptrs)
>     zipWithM_ (initNode . snd) allocs ptrs
>     next
>   where vs = map fst allocs
>         initNode init ptr = init ptr
>         uninitialized v = error ("Uninitialized node " ++ show v)

> initChar :: Char -> NodePtr -> MachStateT ()
> initChar c ptr = updateNode ptr (CharNode c)

> initInt :: Integer -> NodePtr -> MachStateT ()
> initInt i ptr = updateNode ptr (IntNode i)

> initFloat :: Double -> NodePtr -> MachStateT ()
> initFloat f ptr = updateNode ptr (FloatNode f)

> initConstr :: NodeTag -> [String] -> NodePtr -> MachStateT ()
> initConstr (ConstructorTag t c n) vs ptr
>   | length vs == n =
>       readState (getVars vs) >>= updateNode ptr . ConstructorNode t c
>   | otherwise = fail "Type error in initConstr"

> initClosure :: Function -> [String] -> NodePtr -> MachStateT ()
> initClosure (f,code,n) vs ptr
>   | length vs <= n =
>       readState (getVars vs) >>= updateNode ptr . ClosureNode f n code
>   | otherwise = fail "Type error in initClosure"

> initLazy :: Function -> [String] -> NodePtr -> MachStateT ()
> initLazy (f,code,n) vs ptr
>   | length vs == n =
>       readState (getVars vs) >>= updateNode ptr . LazyNode f n code
>   | otherwise = fail "Type error in initLazy"

> initFree :: NodePtr -> MachStateT ()
> initFree ptr = updateNode ptr (VarNode [] [])

> initIndir :: String -> NodePtr -> MachStateT ()
> initIndir v ptr = readState (getVar v) >>= updateNode ptr . IndirNode

> initQueueMe :: NodePtr -> MachStateT ()
> initQueueMe ptr = updateNode ptr (QueueMeNode [])

\end{verbatim}
As a matter of convenience, we also provide some allocation functions,
which initialize fresh nodes directly.
\begin{verbatim}

> allocChar :: Char -> MachStateT NodePtr
> allocChar c = read'updateState (allocNode (CharNode c))

> allocInt :: Integer -> MachStateT NodePtr
> allocInt i = read'updateState (allocNode (IntNode i))

> allocFloat :: Double -> MachStateT NodePtr
> allocFloat f = read'updateState (allocNode (FloatNode f))

> allocData :: Int -> String -> [NodePtr] -> MachStateT NodePtr
> allocData t c ptrs = read'updateState (allocNode (ConstructorNode t c ptrs))

> allocVariables :: Int -> MachStateT [NodePtr]
> allocVariables n = read'updateState (allocNodes (replicate n (VarNode [] [])))

> allocClosure :: Function -> [NodePtr] -> MachStateT NodePtr
> allocClosure (f,code,n) ptrs
>   | length ptrs <= n =
>       read'updateState (allocNode (ClosureNode f n code ptrs))
>   | otherwise = fail "Type error in allocClosure"

> allocLazy :: Function -> [NodePtr] -> MachStateT NodePtr
> allocLazy (f,code,n) ptrs
>   | length ptrs == n = read'updateState (allocNode (LazyNode f n code ptrs))
>   | otherwise = fail "Type error in allocLazy"

\end{verbatim}
\subsubsection{Evaluation of Nodes}
An \texttt{eval} statement starts the evaluation of the referenced
node to weak head normal form. When the node is already in weak head
normal form it is returned to the caller. If the node is a lazy
application, it will be overwritten with a queue-me node that is later
overwritten with the result of the application. If the node is a
global application, the current search is suspended and the global
node is evaluated by the enclosing computation.
\begin{verbatim}

> enter :: String -> Instruction
> enter v = readState (getVar v) >>= enter
>   where enter ptr = deref ptr >>= enterNode ptr
>         enterNode _ (ClosureNode _ n code ptrs)
>           | length ptrs == n =
>               do
>                 updateState (pushNodes ptrs)
>                 code
>         enterNode ptr lazy@(LazyNode f n code ptrs)
>           | length ptrs == n =
>               do
>                 updateState (saveBinding ptr lazy)
>                 updateNode ptr (QueueMeNode [])
>                 updateState (pushNode ptr)
>                 updateState (pushCont update)
>                 updateState (pushNodes ptrs)
>                 code
>           | otherwise = fail "Wrong number of arguments in lazy application"
>         enterNode ptr lazy@(QueueMeNode wq) =
>           do
>             thd <- readState (suspendThread (resume ptr))
>             updateState (saveBinding ptr lazy)
>             updateNode ptr (QueueMeNode (thd:wq))
>             switchContext
>         enterNode _ (IndirNode ptr) = deref ptr >>= enterNode ptr
>         enterNode ptr lazy@(GlobalAppNode _ _) =
>           suspendSearch ptr lazy (resume ptr)
>         enterNode ptr _ = retNode ptr
>         resume ptr = deref ptr >>= resumeNode ptr
>         resumeNode _ (LazyNode _ _ _ _) =
>           fail "Indirection to unevaluated lazy application node"
>         resumeNode _ (QueueMeNode _) =
>           fail "Indirection to locked lazy application node"
>         resumeNode _ (IndirNode ptr) = deref ptr >>= resumeNode ptr
>         resumeNode ptr _ = retNode ptr
>         update = read'updateState popNodes2 >>= uncurry update'
>         update' ptr lptr = deref lptr >>= updateLazy ptr lptr
>         updateLazy ptr lptr lazy@(QueueMeNode wq) =
>           do
>             updateState (saveBinding lptr lazy)
>             updateNode lptr (IndirNode ptr)
>             updateState (pushNode ptr)
>             updateState (wakeThreads wq)
>             ret
>         updateLazy _ _ (LazyNode _ _ _ _) =
>           fail "Unlocked lazy application in update frame"
>         updateLazy _ _ _ = fail "No lazy application in update frame"

\end{verbatim}
\subsubsection{Function Evaluation}
A function call pushes the arguments onto the data stack and enters
the specified function. Upon entry, the called function initializes a
fresh local environment with the nodes from the data stack and then
executes its code. At the end, the function returns to the current
context from either the return or the update stack. If both stacks are
empty, the current thread terminates which eventually may cause a
deadlock.
\begin{verbatim}

> exec :: Function -> [String] -> Instruction
> exec (_,code,n) vs
>   | length vs == n =
>       do
>         readState (getVars vs) >>= updateState . pushNodes
>         code
>   | otherwise = fail "Wrong number of arguments in Exec"

> entry :: [String] -> Instruction -> Instruction
> entry vs body =
>   do
>     updateState initEnv
>     read'updateState (popNodes (length vs)) >>= updateState . setVars vs
>     body

> ret :: Instruction
> ret = read'updateState popCont >>= maybe switchContext id

> switchContext :: Instruction
> switchContext = read'updateState runThread >>= maybe deadlock id
>   where deadlock = readState curContext >>= deadlock'
>         deadlock' IOContext = readState (return . Just)
>         deadlock' GlobalContext = readState (return . Just)
>         deadlock' _ = stoppedSearch

\end{verbatim}
\texttt{Ccall} statements are intended for implementing calls to
foreign primitives written in C. We emulate such calls here by mapping
them onto a set of predefined functions (defined in
Sect.~\ref{sec:mach-arithmetic}).
\begin{verbatim}

> type Primitive = (String,[NodePtr] -> MachStateT NodePtr)

> cCall :: Primitive -> [String] -> Instruction
> cCall (_,code) vs = readState (getVars vs) >>= code >>= retNode

> prim1 ::  Monad m => (NodePtr -> m a) -> [NodePtr] -> m a
> prim1 code [ptr] = code ptr
> prim1 _ _ = fail "Wrong number of arguments in CCall"

> prim2 :: Monad m => (NodePtr -> NodePtr -> m a) -> [NodePtr] -> m a
> prim2 code [ptr1,ptr2] = code ptr1 ptr2
> prim2 _ _ = fail "Wrong number of arguments in CCall"

\end{verbatim}
\subsubsection{Case Selection}
A \texttt{switch} statement selects the code branch matched by
the tag of the specified node. Depending on the mode of the switch
statement, an unbound variable either suspends the current thread
until the variable is instantiated (\texttt{rigid}) or instantiates
the variable non-deterministically (\texttt{flex}). If no case
matches, the default action is chosen. Global variables are never
instantiated. Instead, the current search is suspended until the
variable is instantiated in the enclosing computation.

After instantiating a variable, the abstract machine checks that all
constraints on the variable are still entailed and then wakes all
threads from the variable's wait queue. If the variable is bound to
another variable, the wait queues are concatenated instead of waking
the suspended threads. In addition, we must check the constraints of
the other variable as well because both constraint lists can include a
disequality between the variables. If a variable is bound to a global
variable and the local variable has constraints or blocked threads, we
must suspend the current search until the global variable is
instantiated.

Note that \texttt{bindVar} must check whether the variable node has
been bound already. This may happen if a search strategy restricts the
search space of a goal by instantiating the goal variable to a
non-variable term. For instance, in
\begin{verbatim}
  main = concatMap try (map (`inject` nonNull) (try goal))
  goal xs = length xs =:= 1
  nonNull (_:_) = success
\end{verbatim}
the goal variable is bound to a list node before the search
continuations are resumed that were returned by the inner \texttt{try}
application.
\begin{verbatim}

> switchRigid :: String -> [(NodeTag,NodePtr -> Instruction)]
>             -> (NodePtr -> Instruction) -> Instruction
> switchRigid v dispatchTable dflt = rigidSwitch
>   where rigidSwitch = switch v dispatchTable' dflt
>         dispatchTable' =
>           (VariableTag,delay rigidSwitch) :
>           (GlobalVarTag,delaySearch rigidSwitch) :
>           dispatchTable

> delay :: Instruction -> NodePtr -> Instruction
> delay cont vptr = deref vptr >>= delayNode vptr
>   where delayNode vptr var@(VarNode cs wq) =
>           do
>             thd <- readState (suspendThread cont)
>             updateState (saveBinding vptr var)
>             updateNode vptr (VarNode cs (thd:wq))
>             switchContext

> switchFlex :: String -> [(NodeTag,NodePtr -> Instruction)]
>            -> (NodePtr -> Instruction) -> Instruction
> switchFlex v dispatchTable dflt = flexSwitch
>   where flexSwitch = switch v dispatchTable' dflt
>         dispatchTable'
>           | null alts = dispatchTable
>           | otherwise =
>               (VariableTag,tryBind alts flexSwitch) :
>               (GlobalVarTag,delaySearch flexSwitch) :
>               dispatchTable
>         alts = map instantiate dispatchTable

> tryBind :: [NodePtr -> Instruction] -> Instruction -> NodePtr -> Instruction
> tryBind (alt:alts) cont vptr = deref vptr >>= tryBindNode vptr
>   where tryBindNode vptr var@(VarNode cs wq)
>           | null alts = alt vptr
>           | otherwise =
>               do
>                 thd <- read'updateState (yieldSuspendThread (resume vptr))
>                 case thd of
>                   Just thd ->
>                     do
>                       updateState (saveBinding vptr var)
>                       updateNode vptr (VarNode cs (thd:wq))
>                       switchContext
>                   Nothing -> choice vptr
>         resume ptr = deref ptr >>= resumeNode ptr
>         resumeNode _ (IndirNode ptr) = resume ptr
>         resumeNode ptr (VarNode _ _) = choice ptr
>         resumeNode _ _ = cont
>         choice vptr = tryChoice (map ($ vptr) (alt:alts))

> delaySearch :: Instruction -> NodePtr -> Instruction
> delaySearch cont vptr = deref vptr >>= flip (suspendSearch vptr) cont

> instantiate ::(NodeTag,NodePtr -> Instruction) -> NodePtr -> Instruction
> instantiate (tag,body) vptr =
>   do
>     var <- deref vptr
>     ptr <- freshNode tag
>     bindVar vptr var ptr (body ptr)
>   where freshNode (CharTag c) = allocChar c
>         freshNode (IntTag i) = allocInt i
>         freshNode (FloatTag f) = allocFloat f
>         freshNode (ConstructorTag t c n) = allocVariables n >>= allocData t c

> bindVar :: NodePtr -> Node -> NodePtr -> Instruction -> Instruction
> bindVar vptr var@(VarNode cs wq) ptr next = deref ptr >>= bindVarNode ptr
>   where bindVarNode _ (IndirNode ptr) = deref ptr >>= bindVarNode ptr
>         bindVarNode ptr node@(VarNode cs2 wq2) =
>           do
>             updateState (saveBinding vptr var)
>             updateNode vptr (IndirNode ptr)
>             updateState (saveBinding ptr node)
>             updateNode ptr (VarNode [] (wq ++ wq2))
>             checkConstraints ptr (cs ++ cs2) next
>         bindVarNode ptr node@(GlobalVarNode _ _) =
>           if null cs && null wq then
>             do
>               updateState (saveBinding vptr var)
>               updateNode vptr (IndirNode ptr)
>               next
>           else
>             suspendSearch ptr node (bindVar vptr var ptr next)
>         bindVarNode ptr _ =
>           do
>             updateState (saveBinding vptr var)
>             updateNode vptr (IndirNode ptr)
>             checkConstraints ptr cs (wakeQueue wq next)
> bindVar vptr _ ptr next = bindUnify vptr ptr next

> bindUnify :: NodePtr -> NodePtr -> Instruction -> Instruction
> bindUnify ptr1 ptr2 next =
>   do
>     updateState (pushCont (read'updateState popNode >> next))
>     unifyTerms ptr1 ptr2

> checkConstraints :: NodePtr -> [Constraint] -> Instruction -> Instruction
> checkConstraints _ [] next = next
> checkConstraints ptr (DisEq ptr':cs) next =
>   do
>     updateState (pushNodes [ptr,ptr'])
>     updateState
>       (pushCont (read'updateState popNode >> checkConstraints ptr cs next))
>     diseqCode

> wakeQueue :: ThreadQueue -> Instruction -> Instruction
> wakeQueue tq next = if null tq then next else wake tq next
>   where wake tq next =
>           do
>             updateState (interruptThread next)
>             updateState (wakeThreads tq)
>             switchContext

> switch :: String -> [(NodeTag,NodePtr -> Instruction)]
>        -> (NodePtr -> Instruction) -> Instruction
> switch v dispatchTable dflt = readState (getVar v) >>= switch
>   where dispatchTable' = (IndirTag,switchIndir) : dispatchTable
>         switch ptr = deref ptr >>= switchNode ptr
>         switchNode ptr node =
>           maybe dflt id (lookup (nodeTag node) dispatchTable') ptr
>         switchIndir iptr =
>           do
>             IndirNode ptr <- deref iptr
>             updateState (setVar v ptr)
>             switch ptr

> bindArgs :: (NodePtr -> MachStateT ()) -> Instruction
>          -> NodePtr -> Instruction
> bindArgs bind next ptr =
>   do
>     bind ptr
>     next

> bindLiteral :: NodePtr -> MachStateT ()
> bindLiteral _ = return ()

> bindData :: [String] -> NodePtr -> MachStateT ()
> bindData vs ptr = deref ptr >>= bindConstrNode vs
>   where bindConstrNode vs (ConstructorNode _ _ ptrs)
>           | length vs == length ptrs = updateState (setVars vs ptrs)
>           | otherwise = fail "Type error in switch case"

\end{verbatim}
\subsubsection{Non-deterministic Evaluation}
A \texttt{choice} statement executes its alternatives
non-deterministically. If there are other threads which can proceed
with a deterministic computation, the current thread is suspended
until these threads either finish or suspend.
\begin{verbatim}

> choice :: [Instruction] -> Instruction
> choice [] = failAndBacktrack
> choice (alt:alts)
>   | null alts = alt
>   | otherwise = read'updateState (yieldThread try) >>= \so ->
>                 if so then switchContext else try
>   where try = tryChoice (alt:alts)

> tryChoice :: [Instruction] -> Instruction
> tryChoice (alt:alts) = readState curContext >>= try
>   where try IOContext = fail "Cannot duplicate the world"
>         try GlobalContext =
>           do
>             updateState (pushChoicepoint (tryNext alts))
>             alt
>         try _ = choiceSearch (alt:alts)
>         tryNext (alt:alts) =
>           do
>             updateState (updChoicepoint alts)
>             alt
>         updChoicepoint alts
>           | null alts = popChoicepoint
>           | otherwise = updateChoicepoint (tryNext alts)

> failAndBacktrack :: Instruction
> failAndBacktrack = readState curContext >>= fail
>   where fail IOContext = return Nothing
>         fail GlobalContext =
>           read'updateState backtrack >>= maybe (return Nothing) id
>         fail _ = failSearch

\end{verbatim}
\subsubsection{Sequencing of Instructions}
A statement sequence $x$ \texttt{<-} \emph{st$_1$}\texttt{;}
\emph{st$_2$} binds $x$ to the result of \emph{st$_1$} and then
executes \emph{st$_2$} in the extended environment.
\begin{verbatim}

> seqStmts :: String -> Instruction -> Instruction -> Instruction
> seqStmts v first next =
>   do
>     updateState (pushCont bindCont)
>     first
>   where bindCont =
>           do
>             read'updateState popNode >>= updateState . setVar v
>             next

\end{verbatim}
\subsection{Primitives}
\subsubsection{Application Functions}
There is a -- potentially -- unlimited number of functions
\texttt{@}$i$, which are used by the compiler for implementing
applications of a function variable to $i$ arguments.\footnote{For
historical reasons, the compiler uses \texttt{@} instead of
\texttt{@1}.}
\begin{verbatim}

> applyFunction :: Function
> applyFunction = ("@",applyCode 1,2)

> applyFunctions :: [Function]
> applyFunctions = applyFunction : [('@':show i,applyCode i,i+1) | i <- [2..]]

> applyCode :: Int -> Instruction
> applyCode n =
>   entry ("f" : xs) $
>   do
>     ptrs <- readState (getVars xs)
>     seqStmts "_f" (enter "f")
>          (switchRigid "_f" [(ClosureTag,apply ptrs)]
>                       (const (fail "@: bad argument type!")))
>   where xs = ['x':show i | i <- [1..n]]
>         apply ptrs fptr = deref fptr >>= enterNode ptrs
>         enterNode ptrs' (ClosureNode f n code ptrs) =
>           applyClosure f code n (ptrs ++ ptrs')
>         enterNode _ _ = fail "Type error in Exec: not a function"
>         applyClosure f code n ptrs
>           | length ptrs < n = allocClosure (f,code,n) ptrs >>= retNode
>           | otherwise =
>               do
>                 let (ptrs',ptrs'') = splitAt n ptrs
>                 unless (null ptrs'')
>                        (updateState (pushNodes ptrs'') >>
>                         updateState (pushCont (applyCode (length ptrs''))))
>                 updateState (pushNodes ptrs')
>                 code

\end{verbatim}
In order to handle partial applications of data constructors, the
compiler provides an auxiliary function for each data constructor,
which returns a new constructor node with the supplied arguments.
\begin{verbatim}

> constrFunction :: Int -> String -> Int -> Function
> constrFunction t c n = (c,constrCode t c n,n)

> constrCode :: Int -> String -> Int -> Instruction
> constrCode t c n = read'updateState (popNodes n) >>= allocData t c >>= retNode

\end{verbatim}
\subsubsection{Arithmetic Operations}\label{sec:mach-arithmetic}
All arithmetic operations are implemented as primitives.
\begin{verbatim}

> ordPrimitive,chrPrimitive :: Primitive
> ordPrimitive = ("primOrd",prim1 primOrd)
> chrPrimitive = ("primChr",prim1 primChr)

> primOrd, primChr :: NodePtr -> MachStateT NodePtr
> primOrd = withChar "ord" (allocInt . toInteger . ord)
> primChr = withInt "chr" (allocChar . chr . fromInteger)

> addIntPrimitive, subIntPrimitive, mulIntPrimitive :: Primitive
> quotIntPrimitive, remIntPrimitive :: Primitive
> divIntPrimitive, modIntPrimitive :: Primitive
> addIntPrimitive = ("primAddInt", prim2 $ primIntOp "+" (+))
> subIntPrimitive = ("primSubInt", prim2 $ primIntOp "-" (-))
> mulIntPrimitive = ("primMulInt", prim2 $ primIntOp "*" (*))
> quotIntPrimitive = ("primQuotInt", prim2 $ primIntOp "quot" quot)
> remIntPrimitive = ("primRemInt", prim2 $ primIntOp "rem" rem)
> divIntPrimitive = ("primDivInt", prim2 $ primIntOp "div" div)
> modIntPrimitive = ("primModInt", prim2 $ primIntOp "mod" mod)

> primIntOp :: String -> (Integer -> Integer -> Integer) -> NodePtr -> NodePtr
>           -> MachStateT NodePtr
> primIntOp what op x y =
>   withInt what (\i -> withInt what (\j -> allocInt (i `op` j)) y) x

> addFloatPrimitive, subFloatPrimitive :: Primitive
> mulFloatPrimitive, divFloatPrimitive :: Primitive
> addFloatPrimitive = ("primAddFloat", prim2 $ primFloatOp "+." (+))
> subFloatPrimitive = ("primSubFloat", prim2 $ primFloatOp "-." (-))
> mulFloatPrimitive = ("primMulFloat", prim2 $ primFloatOp "*." (*))
> divFloatPrimitive = ("primDivFloat", prim2 $ primFloatOp "/." (/))

> primFloatOp :: String -> (Double -> Double -> Double) -> NodePtr -> NodePtr
>             -> MachStateT NodePtr
> primFloatOp what op x y =
>  withFloat what (\e -> withFloat what (\f -> allocFloat (e `op` f)) y) x

> floatPrimitive :: Primitive
> floatPrimitive = ("primFloat", prim1 primFloat)

> primFloat :: NodePtr -> MachStateT NodePtr
> primFloat = withInt "floatFromInt" (allocFloat . fromIntegral)

> truncPrimitive, roundPrimitive :: Primitive
> truncPrimitive = ("primTrunc", prim1 $ primFromFloat "truncateFloat" truncate)
> roundPrimitive = ("primRound", prim1 $ primFromFloat "roundFloat" round)

> primFromFloat :: String -> (Double -> Integer) -> NodePtr
>               -> MachStateT NodePtr
> primFromFloat what fromDouble = withFloat what (allocInt . fromDouble)

> withChar :: String -> (Char -> MachStateT a) -> NodePtr -> MachStateT a
> withChar what code ptr = deref ptr >>= withCharNode code
>   where withCharNode code (CharNode c) = code c
>         withCharNode _ _ = fail (what ++ ": invalid argument")

> withInt :: String -> (Integer -> MachStateT a) -> NodePtr -> MachStateT a
> withInt what code ptr = deref ptr >>= withIntNode code
>   where withIntNode code (IntNode i) = code i
>         withIntNode _ _ = fail (what ++ ": invalid argument")

> withFloat :: String -> (Double -> MachStateT a) -> NodePtr -> MachStateT a
> withFloat what code ptr = deref ptr >>= withFloatNode code
>   where withFloatNode code (FloatNode f) = code f
>         withFloatNode _ _ = fail (what ++ ": invalid argument")

\end{verbatim}
\subsubsection{Comparing Nodes}
The operator \texttt{(==)} compares two data terms for equality and
returns either \texttt{True} or \texttt{False}. In contrast to
equality constraints, this function is rigid. In addition, we support
equality checks only for literals and data terms, but not for partial
applications.
\begin{verbatim}

> equalFunction :: Function
> equalFunction = ("==",equalCode,2)

> withNode :: (Node -> Instruction) -> NodePtr -> Instruction
> withNode next ptr = deref ptr >>= next

> falseTag, trueTag :: NodeTag
> falseTag = ConstructorTag 0 "False" 0
> trueTag = ConstructorTag 1 "True" 0

> false, true :: MachStateT NodePtr
> false = read'updateState (atom falseTag)
> true = read'updateState (atom trueTag)

> bool :: Bool -> MachStateT NodePtr
> bool False = false
> bool True = true

> equalCode :: Instruction
> equalCode =
>   entry ["x","y"] $ seqStmts "_x" (enter "x")
>                   $ switchRigid "_x" [] (withNode equalNode)
>   where equalNode node =
>           seqStmts "_y" (enter "y")
>                (switchRigid "_y" [] (withNode (equalNodes node)))

> equalNodes :: Node -> Node -> Instruction
> equalNodes (CharNode c) (CharNode d) = bool (c == d) >>= retNode
> equalNodes (IntNode i) (IntNode j) = bool (i == j) >>= retNode
> equalNodes (FloatNode f) (FloatNode g) = bool (f == g) >>= retNode
> equalNodes (ConstructorNode t1 _ ptrs1) (ConstructorNode t2 _ ptrs2)
>   | t1 == t2 = equalArgs (zip ptrs1 ptrs2)
>   | otherwise = false >>= retNode
> equalNodes (ClosureNode f1 _ _ ptrs1) (ClosureNode f2 _ _ ptrs2)
>   | f1 == f2 && length ptrs1 == length ptrs2 = equalArgs (zip ptrs1 ptrs2)
>   | otherwise = false >>= retNode
> equalNodes _ _ = failAndBacktrack

> equalArgs :: [(NodePtr,NodePtr)] -> Instruction
> equalArgs [] = true >>= retNode
> equalArgs ((ptr1,ptr2):ptrs) =
>   do
>     updateState (pushNodes [ptr1,ptr2])
>     unless (null ptrs)
>       (updateState (pushCont (read'updateState popNode >>= equalRest ptrs)))
>     equalCode

> equalRest :: [(NodePtr,NodePtr)] -> NodePtr -> Instruction
> equalRest ptrs ptr =
>   do
>     node <- deref ptr
>     if nodeTag node == trueTag then equalArgs ptrs else retNode ptr

\end{verbatim}
The \texttt{compare} function compares two data terms and returns one
of the values \texttt{LT}, \texttt{EQ}, \texttt{GT} defined in the
\texttt{Prelude}.
\begin{verbatim}

> compareFunction :: Function
> compareFunction = ("compare",compareCode,2)

> ltTag, eqTag, gtTag :: NodeTag
> ltTag = ConstructorTag 0 "LT" 0
> eqTag = ConstructorTag 1 "EQ" 0
> gtTag = ConstructorTag 2 "GT" 0

> lt, eq, gt :: MachStateT NodePtr
> lt = read'updateState (atom ltTag)
> eq = read'updateState (atom eqTag)
> gt = read'updateState (atom gtTag)

> order :: Ordering -> MachStateT NodePtr
> order LT = lt
> order EQ = eq
> order GT = gt

> compareCode :: Instruction
> compareCode =
>   entry ["x","y"] $ seqStmts "_x" (enter "x")
>                   $ switchRigid "_x" [] (withNode compareNode)
>   where compareNode node =
>           seqStmts "_y" (enter "y")
>                (switchRigid "_y" [] (withNode (compareNodes node)))

> compareNodes :: Node -> Node -> Instruction
> compareNodes (CharNode c) (CharNode d) = order (compare c d) >>= retNode
> compareNodes (IntNode i) (IntNode j) = order (compare i j) >>= retNode
> compareNodes (FloatNode f) (FloatNode g) = order (compare f g) >>= retNode
> compareNodes (ConstructorNode t1 _ ptrs1) (ConstructorNode t2 _ ptrs2) =
>   case compare t1 t2 of
>     EQ -> compareArgs (zip ptrs1 ptrs2)
>     cmp -> order cmp >>= retNode
> compareNodes _ _ = failAndBacktrack

> compareArgs :: [(NodePtr,NodePtr)] -> Instruction
> compareArgs [] = order EQ >>= retNode
> compareArgs ((ptr1,ptr2):ptrs) =
>   do
>     updateState (pushNodes [ptr1,ptr2])
>     unless (null ptrs)
>       (updateState (pushCont (read'updateState popNode >>= compareRest ptrs)))
>     compareCode

> compareRest :: [(NodePtr,NodePtr)] -> NodePtr -> Instruction
> compareRest ptrs ptr =
>   do
>     node <- deref ptr
>     if nodeTag node == eqTag then compareArgs ptrs else retNode ptr

\end{verbatim}
\subsubsection{Concurrent Conjunction}
The concurrent conjunction operator \texttt{\&} evaluates two
constraints concurrently. It tries to avoid the creation of a
new thread whenever this is possible. Note that the result of
\texttt{\&} may be an unbound variable.
\begin{verbatim}

> success :: MachStateT NodePtr
> success = read'updateState (atom successTag)

> concConjFunction :: Function
> concConjFunction = ("&",concConjCode,2)

> concConjCode :: Instruction
> concConjCode =
>   entry ["c1","c2"] $
>   switch "c1"
>          [(LazyTag,suspension),(QueueMeTag,queueMe),(VariableTag,variable),
>           (GlobalAppTag,globalApp),(GlobalVarTag,variable)]
>          (const (enter "c2"))
>   where suspension ptr1 =
>           switch "c2"
>                  [(LazyTag,const (concurrent ptr1)),
>                   (QueueMeTag,const sequential),
>                   (VariableTag,const sequential),
>                   (GlobalAppTag,const (concurrent ptr1)),
>                   (GlobalVarTag,const sequential)]
>                  (const (enter "c1"))
>         queueMe ptr1 =
>           switch "c2"
>                  [(LazyTag,const (flipArguments >> sequential)),
>                   (QueueMeTag,const sequential),
>                   (VariableTag,const sequential),
>                   (GlobalAppTag,const (flipArguments >> sequential)),
>                   (GlobalVarTag,const sequential)]
>                  (const (enter "c1"))
>         variable ptr1 =
>           switch "c2"
>                  [(LazyTag,const (flipArguments >> sequential)),
>                   (QueueMeTag,const (flipArguments >> sequential)),
>                   (VariableTag,wait ptr1),
>                   (GlobalAppTag,const (flipArguments >> sequential)),
>                   (GlobalVarTag,wait ptr1)]
>                  (const (retNode ptr1))
>         globalApp ptr1 =
>           switch "c2"
>                  [(LazyTag,const sequential),
>                   (QueueMeTag,const sequential),
>                   (VariableTag,const sequential),
>                   (GlobalAppTag,const sequential),
>                   (GlobalVarTag,const sequential)]
>                  (const (enter "c1"))
>         concurrent ptr1 =
>           do
>             updateState (interruptThread (flipArguments >> sequential))
>             updateState newThread
>             updateState (setVar "c1" ptr1)
>             enter "c1"
>         sequential = seqStmts "_c1" (enter "c1") sequentialCont
>         sequentialCont =
>           switch "_c1"
>                  [(LazyTag,const (fail "This cannot happen")),
>                   (QueueMeTag,const (fail "This cannot happen")),
>                   (VariableTag,variable),
>                   (GlobalAppTag,const (fail "This cannot happen")),
>                   (GlobalVarTag,variable)]
>                  (const (enter "c2"))
>         wait ptr1 ptr2 =
>           do
>             updateState (setVars ["_c1","_c2"] [ptr1,ptr2])
>             switchRigid "_c1" [] (const (enter "_c2"))
>         flipArguments =
>           do
>             ptr1 <- readState (getVar "c1")
>             ptr2 <- readState (getVar "c2")
>             updateState (setVars ["c1","c2"] [ptr2,ptr1])

\end{verbatim}
\subsubsection{Equality Constraints}
Unification of two arbitrary arguments is a very complex process.
Following the semantics, we have to ensure that both arguments are
evaluated to weak head normal before we actually unify the arguments.
When we have to unify two data constructors or a data constructor and
a variable, we also have to unify of the arguments of the data
constructors, which can proceed concurrently.
\begin{verbatim}

> unifyFunction :: Function
> unifyFunction = ("=:=",unifyCode,2)

> unifyCode :: Instruction
> unifyCode =
>   entry ["x","y"] $ seqStmts "_x" (enter "x")
>                   $ seqStmts "_y" (enter "y") unifyCode'
>   where unifyCode' =
>           do
>             ptr1 <- readState (getVar "_x")
>             ptr2 <- readState (getVar "_y")
>             unifyTerms ptr1 ptr2

> unifyTerms :: NodePtr -> NodePtr -> Instruction
> unifyTerms ptr1 ptr2 =
>   do
>     ptr1 <- derefPtr ptr1
>     node1 <- deref ptr1
>     ptr2 <- derefPtr ptr2
>     node2 <- deref ptr2
>     unifyNodes ptr1 node1 ptr2 node2

> unifyNodes :: NodePtr -> Node -> NodePtr -> Node -> Instruction
> unifyNodes ptr1 var1@(VarNode _ _) ptr2 var2@(VarNode _ _)
>   | ptr1 == ptr2 = unifySuccess
>   | otherwise = bindVar ptr1 var1 ptr2 unifySuccess
> unifyNodes ptr1 var1@(VarNode _ _) ptr2 var2@(GlobalVarNode _ _) =
>   bindVar ptr1 var1 ptr2 unifySuccess
> unifyNodes ptr1 var1@(GlobalVarNode _ _) ptr2 var2@(VarNode _ _) =
>   bindVar ptr2 var2 ptr1 unifySuccess
> unifyNodes ptr1 var1@(GlobalVarNode _ _) ptr2 var2@(GlobalVarNode _ _)
>   | ptr1 == ptr2 = unifySuccess
>   | otherwise = suspendSearch ptr1 var1 (unifyTerms ptr1 ptr2)
> unifyNodes ptr1 var@(VarNode _ _) ptr2 node =
>   occursCheck ptr1 node >>= \occurs ->
>   if occurs then
>     failAndBacktrack
>   else
>     do
>       (ptr',ptrs) <- freshTerm ptr2 node
>       bindVar ptr1 var ptr' (unifyArgs ptrs)
> unifyNodes ptr1 node ptr2 var@(VarNode _ _) =
>   unifyNodes ptr2 var ptr1 node
> unifyNodes _ (CharNode c) _ (CharNode d)
>   | c == d = unifySuccess
>   | otherwise = failAndBacktrack
> unifyNodes _ (IntNode i) _ (IntNode j)
>   | i == j = unifySuccess
>   | otherwise = failAndBacktrack
> unifyNodes _ (FloatNode f) _ (FloatNode g)
>   | f == g = unifySuccess
>   | otherwise = failAndBacktrack
> unifyNodes _ (ConstructorNode t1 _ ptrs1) _ (ConstructorNode t2 _ ptrs2)
>   | t1 == t2 && length ptrs1 == length ptrs2 = unifyArgs (zip ptrs1 ptrs2)
>   | otherwise = failAndBacktrack
> unifyNodes _ (ClosureNode f1 _ _ ptrs1) _ (ClosureNode f2 _ _ ptrs2)
>   | f1 == f2 && length ptrs1 == length ptrs2 = unifyArgs (zip ptrs1 ptrs2)
>   | otherwise = failAndBacktrack
> unifyNodes ptr1 (SearchContinuation _ _ _ _) ptr2 (SearchContinuation _ _ _ _)
>   | ptr1 == ptr2 = unifySuccess
>   | otherwise = failAndBacktrack
> unifyNodes _ _ _ _ = failAndBacktrack

> unifyArgs :: [(NodePtr,NodePtr)] -> Instruction
> unifyArgs [] = unifySuccess
> unifyArgs ((ptr1,ptr2) : ptrs)
>   | null ptrs =
>       do
>         updateState (pushNodes [ptr1,ptr2])
>         unifyCode
>   | otherwise =
>       do
>         lazy <- allocLazy unifyFunction [ptr1,ptr2]
>         updateState (setVar "c" lazy)
>         updateState (interruptThread (unifyRest ptrs))
>         updateState newThread
>         updateState (setVar "c" lazy)
>         enter "c"
>   where unifyRest ptrs =
>           switch "c"
>                  [(LazyTag,const (fail "This cannot happen")),
>                   (QueueMeTag,unifyRest' ptrs),
>                   (VariableTag,const (fail "This cannot happen"))]
>                  (const (unifyArgs ptrs))
>         unifyRest' ptrs lazy =
>           do
>             updateState (pushCont unifyCont)
>             unifyArgs ptrs
>         unifyCont =
>           do
>             read'updateState popNode
>             enter "c"

> unifySuccess :: Instruction
> unifySuccess = success >>= retNode

> occursCheck :: NodePtr -> Node -> MachStateT Bool
> occursCheck vptr (ConstructorNode _ _ args)
>   | any (vptr ==) args = return True
>   | otherwise = occursCheckArgs vptr args
> occursCheck vptr (IndirNode ptr)
>   | vptr == ptr = return True
>   | otherwise = deref ptr >>= occursCheck vptr
> occursCheck _ _ = return False

> occursCheckArgs :: NodePtr -> [NodePtr] -> MachStateT Bool
> occursCheckArgs _ [] = return False
> occursCheckArgs vptr (ptr:ptrs) =
>   deref ptr >>= occursCheck vptr >>= \occurs ->
>   if occurs then return True else occursCheckArgs vptr ptrs

> freshTerm :: NodePtr -> Node -> MachStateT (NodePtr,[(NodePtr,NodePtr)])
> freshTerm ptr (ConstructorNode t c ptrs)
>   | null ptrs = return (ptr,[])
>   | otherwise =
>       do
>         vars <- allocVariables (length ptrs)
>         ptr' <- allocData t c vars
>         return (ptr',zip vars ptrs)
> freshTerm ptr (ClosureNode f n code ptrs)
>   | null ptrs = return (ptr,[])
>   | length ptrs < n =
>       do
>         vars <- allocVariables (length ptrs)
>         ptr' <- allocClosure (f,code,n) vars
>         return (ptr',zip vars ptrs)
>   | otherwise = fail (f ++ " applied to too many arguments")
> freshTerm ptr _ = return (ptr,[])

\end{verbatim}
\subsubsection{Disequality Constraints}
Disequality constraints are implemented by the primitive function
\texttt{=/=}. This function evaluates both arguments to head normal
form, first. If one argument is a (local) variable node, the other
argument is evaluated to normal form and added as a constraint to the
variable. Otherwise the tags of both arguments are compared and if
they match the disequality is distributed over the arguments of the
data constructors.

\ToDo{Do not add redundant constraints to a variable, e.g., if a
variable $x$ is already constrained to be different from $y$ it is not
necessary to add the constraint $\not= x$ to $y$.}

\ToDo{Avoid the distribution of argument disequalities when this is
possible. For instance, it is not necessary to split the computation
for the disequality \texttt{(0:xs) =/= [0]}.}
\begin{verbatim}

> diseqFunction :: Function
> diseqFunction = ("=/=",diseqCode,2)

> diseqCode :: Instruction
> diseqCode =
>   entry ["x","y"] $ seqStmts "_x" (enter "x")
>                   $ seqStmts "_y" (enter "y") diseqCode'
>   where diseqCode' =
>           do
>             ptr1 <- readState (getVar "_x")
>             ptr2 <- readState (getVar "_y")
>             diseqTerms ptr1 ptr2

> diseqTerms :: NodePtr -> NodePtr -> Instruction
> diseqTerms ptr1 ptr2 =
>   do
>     ptr1 <- derefPtr ptr1
>     node <- deref ptr1
>     ptr2 <- derefPtr ptr2
>     node' <- deref ptr2
>     diseqNodes ptr1 node ptr2 node'

> diseqNodes :: NodePtr -> Node -> NodePtr -> Node -> Instruction
> diseqNodes ptr1 var1@(VarNode cs1 wq1) ptr2 var2@(VarNode cs2 wq2)
>   | ptr1 == ptr2 = failAndBacktrack
>   | otherwise =
>       do
>         updateState (saveBinding ptr1 var1)
>         updateNode ptr1 (VarNode (DisEq ptr2 : cs1) wq1)
>         diseqSuccess
> diseqNodes ptr1 var1@(VarNode cs1 wq1) ptr2 var2@(GlobalVarNode _ _) =
>   do
>     updateState (saveBinding ptr1 var1)
>     updateNode ptr1 (VarNode (DisEq ptr2 : cs1) wq1)
>     diseqSuccess
> diseqNodes ptr1 var1@(GlobalVarNode _ _) ptr2 var2@(VarNode cs2 wq2) =
>   do
>     updateState (saveBinding ptr2 var2)
>     updateNode ptr1 (VarNode (DisEq ptr1 : cs2) wq2)
>     diseqSuccess
> diseqNodes ptr1 var1@(GlobalVarNode _ _) ptr2 var2@(GlobalVarNode _ _)
>   | ptr1 == ptr2 = failAndBacktrack
>   | otherwise = suspendSearch ptr1 var1 (diseqTerms ptr1 ptr2)
> diseqNodes ptr1 var@(VarNode cs wq) ptr2 node =
>   occursCheck ptr1 node >>= \occurs ->
>   if occurs then
>     diseqSuccess
>   else
>     do
>       updateState (saveBinding ptr1 var)
>       (ptr',ptrs) <- freshTerm ptr2 node
>       updateNode ptr1 (VarNode (DisEq ptr2 : cs) wq)
>       -- force evaluation of arguments to data terms!
>       unifyArgs (map (\(_,ptr) -> (ptr,ptr)) ptrs)
> diseqNodes ptr1 node ptr2 var@(VarNode _ _) =
>   diseqNodes ptr2 var ptr1 node
> diseqNodes _ (CharNode c) _ (CharNode d)
>   | c /= d = diseqSuccess
>   | otherwise = failAndBacktrack
> diseqNodes _ (IntNode i) _ (IntNode j)
>   | i /= j = diseqSuccess
>   | otherwise = failAndBacktrack
> diseqNodes _ (FloatNode f) _ (FloatNode g)
>   | f /= g = diseqSuccess
>   | otherwise = failAndBacktrack
> diseqNodes _ (ConstructorNode t1 _ ptrs1) _ (ConstructorNode t2 _ ptrs2)
>   | t1 /= t2 = diseqSuccess
>   | otherwise = diseqArgs (zip ptrs1 ptrs2)
> diseqNodes _ (ClosureNode f1 _ _ ptrs1) _ (ClosureNode f2 _ _ ptrs2)
>   | f1 /= f2 || length ptrs1 /= length ptrs2 = diseqSuccess
>   | otherwise = diseqArgs (zip ptrs1 ptrs2)
> diseqNodes ptr1 (SearchContinuation _ _ _ _) ptr2 (SearchContinuation _ _ _ _)
>   | ptr1 /= ptr2 = diseqSuccess
>   | otherwise = failAndBacktrack
> diseqNodes _ _ _ _ = diseqSuccess

> diseqArgs :: [(NodePtr,NodePtr)] -> Instruction
> diseqArgs [] = failAndBacktrack
> diseqArgs ((ptr1,ptr2) : ptrs)
>   | null ptrs = diseqFirst
>   | otherwise = choice [diseqFirst,diseqArgs ptrs]
>   where diseqFirst = updateState (pushNodes [ptr1,ptr2]) >> diseqCode

> diseqSuccess :: Instruction
> diseqSuccess = success >>= retNode

\end{verbatim}
\subsubsection{Pattern Binding Updates}
Two primitive functions support the implementation of pattern bindings
(cf.\ Sect.~\ref{sec:pattern-bindings}). The function
\texttt{pbUpdate} overwrites a lazy application node with the
application result and the function \texttt{pbReturn} returns a
particular component of a pattern. In contrast to normal updates,
\texttt{pbUpdate} must be prepared to update unevaluated applications
as well as queue-me nodes. The semantics of the function
\texttt{pbReturn} is similar to that of \texttt{(Prelude.\&>)} in that
the first argument is a constraint and \texttt{pbReturn} returns the
second argument when the constraint is satisfied. However, since the
constraint is supposed to update the lazy application node that
evaluates the \texttt{pbReturn} application, it discards its own
update frame.
\begin{verbatim}

> pbUpdateFunction, pbReturnFunction :: Function
> pbUpdateFunction = ("pbUpdate",pbUpdateCode,2)
> pbReturnFunction = ("pbReturn",pbReturnCode,2)

> pbUpdateCode :: Instruction
> pbUpdateCode = read'updateState popNodes2 >>= uncurry update
>   where update lptr ptr = deref lptr >>= updateLazy lptr ptr
>         updateLazy lptr ptr lazy@(LazyNode _ _ _ _) =
>           do
>             updateState (saveBinding lptr lazy)
>             updateNode lptr (IndirNode ptr)
>             success >>= retNode
>         updateLazy lptr ptr lazy@(QueueMeNode wq) =
>           do
>             updateState (saveBinding lptr lazy)
>             updateNode lptr (IndirNode ptr)
>             updateState (wakeThreads wq)
>             success >>= retNode
>         updateLazy _ ptr lazy@(IndirNode lptr) = update lptr ptr
>         updateLazy _ _ _ = fail "Invalid pattern binding update"

> pbReturnCode :: Instruction
> pbReturnCode =
>   read'updateState popCont >>= \_ ->
>   entry ["p","v"] $ seqStmts "_p" (enter "p")
>                   $ switchRigid "_p" [(successTag,const (enter "v"))]
>                   $ const (fail "Type error in pattern binding update")

\end{verbatim}
\subsubsection{Encapsulated Search}
The primitive function \texttt{try} starts the reduction of a search
goal in a new local search space. After evaluating the argument to a
closure (of arity 1), the code creates a new empty search space and an
unbound (goal) variable, applies the search goal to that variable, and
starts reduction of this application. All arguments of the closure are
wrapped in global application nodes, since these nodes correspond to
free variables of the search goal.

\ToDo{Do not wrap atomic nodes at all and use global variable nodes
  for all closure arguments which are in head normal form already.}
\begin{verbatim}

> tryFunction :: Function
> tryFunction = ("try",tryCode,1)

> tryCode :: Instruction
> tryCode =
>   entry ["g"] $ seqStmts "_g" (enter "g")
>               $ switchRigid "_g" [(ClosureTag,solve)]
>               $ const (fail "try: bad argument type!")
>   where solve ptr = deref ptr >>= solveNode
>         solveNode goal =
>           do
>             space <- read'updateState newSearchSpace
>             goalVar <- read'updateState (allocNode (VarNode [] []))
>             goalApp <- applyGoal goal goalVar
>             updateState (pushSearchContext goalApp goalVar space)
>             updateState newThread
>             updateState (setVar "c" goalApp)
>             seqStmts "_c" (enter "c")
>                      $ switchRigid "_c" [(successTag,retNode)]
>                      $ const (fail "try: bad goal result type!")
>         applyGoal (ClosureNode f n code ptrs) var
>           | length ptrs + 1 == n =
>               do
>                 ptrs' <- globalArgs ptrs
>                 read'updateState
>                   (allocNode (LazyNode f n code (ptrs' ++ [var])))
>           | otherwise = fail "try: invalid search goal"

\end{verbatim}
When a computation fails within an encapsulated search, the current
search space is discarded and the corresponding \texttt{try} call
returns an empty list.
\begin{verbatim}

> nil :: MachStateT NodePtr
> nil = read'updateState (atom nilTag)

> failSearch :: Instruction
> failSearch =
>   do
>     updateState discardSearchSpace
>     read'updateState popSearchContext
>     nil >>= retNode

\end{verbatim}
When the ready queue becomes empty inside an encapsulated search, this
may be either due to the goal being successfully evaluated or because
a deadlock has occurred. These cases can be distinguished by looking
at the lazy application created for the goal. If it is in head normal
form and ground, the goal has been solved. In this case, a singleton
list containing a solved goal continuation is returned to the caller,
otherwise the calling thread is suspended.

Because we cannot restore search continuations into an arbitrary
search space, the value bound to the goal variable is copied into the
current search space at the time when the solved goal continuation is
evaluated.
\begin{verbatim}

> list1 :: NodePtr -> MachStateT NodePtr
> list1 x = list [x]

> stoppedSearch :: Instruction
> stoppedSearch =
>   do
>     space <- read'updateState saveSearchSpace
>     (goalApp,goalVar) <- read'updateState popSearchContext
>     node <- derefPtr goalApp >>= deref
>     case node of
>       LazyNode _ _ _ _ -> fail "Search goal not locked!"
>       QueueMeNode _ ->
>         do
>           readState (suspendThread undefined)
>           switchContext
>       _ ->
>         do
>           conts <- derefPtr goalVar >>= flip closeSolvedContinuation space
>           list1 conts >>= retNode

> closeSolvedContinuation :: NodePtr -> SearchSpace -> MachStateT NodePtr
> closeSolvedContinuation goalVar space =
>   allocClosure ("<solved goal>",closureCode goalVar space,1) []
>   where closureCode goalVar goalSpace =
>           do
>             solution <- copyGraph goalSpace goalVar
>             arg <- read'updateState popNode
>             node <- deref arg
>             case node of
>               VarNode _ _ -> bindVar arg node solution unifySuccess
>               _ -> unify arg solution
>         unify arg solution =
>           do
>             updateState (pushNodes [arg,solution])
>             unifyCode

\end{verbatim}
\ToDo{Find a way to restore a search space within an arbitrary other
  search space.}

If a \texttt{choice} statement is executed in a local search space,
the current computation is interrupted and a list with one search
continuation for each alternative is returned from \texttt{try}.
\begin{verbatim}

> list :: [NodePtr] -> MachStateT NodePtr
> list = foldr (\x m -> m >>= cons x) nil
>   where cons hd tl = allocData tag cName [hd,tl]
>         ConstructorTag tag cName 2 = consTag

> choiceSearch :: [Instruction] -> Instruction
> choiceSearch alts =
>   do
>     updateState (interruptThread undefined)
>     rq <- readState saveContinuation
>     spc <- read'updateState saveSearchSpace
>     (goal,var) <- read'updateState popSearchContext
>     mapM (closeContinuation goal var rq spc) alts >>= list >>= retNode

> closeContinuation :: NodePtr -> NodePtr -> ThreadQueue -> SearchSpace ->
>     Instruction -> MachStateT NodePtr
> closeContinuation goal var (Thread id _ ep ds rs : rq) spc next =
>   do
>     cont <- read'updateState
>               (allocNode (SearchContinuation goal var (thd : rq) spc))
>     allocClosure ("<search closure>",closureCode cont,1) []
>   where thd = Thread id next ep ds rs
>         closureCode cont =
>           deref cont >>= \cont' ->
>           case cont' of
>             SearchContinuation goalApp goalVar rq space ->
>               readState curSpace >>= isRootSpace >>= \so ->
>               if so then
>                 do
>                   updateState (restoreSearchSpace space)
>                   updateState (restoreContinuation rq)
>                   arg <- read'updateState popNode
>                   node <- deref arg
>                   case node of
>                     VarNode _ _ ->
>                       bindVar arg node goalVar (continueGoal goalApp)
>                     _ -> unify arg goalVar (continueGoal goalApp)
>               else
>                 fail "Cannot restore search continuation in non-root space"
>             _ -> fail "Bad search continuation"
>         unify arg goalVar next =
>           do
>             updateState (pushNodes [arg,goalVar])
>             updateState (pushCont (read'updateState popNode >> next))
>             unifyCode
>         continueGoal goal =
>           do
>             updateState (setVar "c" goal)
>             enter "c"

\end{verbatim}
When a solved search goal is applied, the solution of the goal is
copied into the current search space using \texttt{copyGraph}. We must
be careful to preserve sharing of variable nodes when they are copied.
In addition, we must copy only local variables. The same would hold
for unevaluated lazy applications. However, the result bound to the
goal variable cannot contain any unevaluated applications. In order to
preserve sharing of local variables, every copied variable is
temporarily bound to its copy. This binding is recorded on the trail
and is undone after the graph has been copied.

Note that we use a temporary search context here to be able to undo
the bindings performed during copying.
\begin{verbatim}

> copyGraph :: SearchSpace -> NodePtr -> MachStateT NodePtr
> copyGraph goalSpace ptr =
>   do
>     curSpace <- readState curSpace
>     updateState (pushSearchContext undefined undefined curSpace)
>     actBindings goalSpace
>     ptr' <- copy goalSpace curSpace ptr
>     readState discardSearchSpace
>     read'updateState popSearchContext
>     return ptr'
>   where copy goalSpace curSpace ptr =
>           deref ptr >>= copyNode goalSpace curSpace ptr
>         copyNode goalSpace curSpace ptr (ConstructorNode tag cName args)
>           | not (null args) =
>               do
>                 args' <- mapM (copy goalSpace curSpace) args
>                 read'updateState
>                   (allocNode (ConstructorNode tag cName args'))
>         copyNode goalSpace curSpace ptr var@(VarNode cs wq) =
>           if null wq then
>             do
>               cs' <- mapM (copyConstraint goalSpace curSpace) cs
>               ptr' <- read'updateState (allocNode (VarNode cs' []))
>               updateState (saveBinding ptr var)
>               updateNode ptr (IndirNode ptr')
>               return ptr'
>           else
>             fail "cannot copy variable with non-empty waitlist"
>         copyNode goalSpace curSpace ptr (ClosureNode name arity code args)
>           | not (null args) =
>               do
>                 args' <- mapM (copy goalSpace curSpace) args
>                 read'updateState
>                   (allocNode (ClosureNode name arity code args'))
>         copyNode _ _ _ (LazyNode _ _ _ _) =
>           fail "cannot copy unevaluated lazy application node"
>         copyNode _ _ _ (QueueMeNode _) =
>           fail "cannot copy locked lazy application node"
>         copyNode goalSpace curSpace ptr (IndirNode ptr') =
>           copy goalSpace curSpace ptr'
>         copyNode goalSpace curSpace ptr (GlobalAppNode ptr' space) =
>           space `isLocalSpaceOf` curSpace >>= \so ->
>           return (if so then ptr' else ptr)
>         copyNode goalSpace curSpace ptr (GlobalVarNode ptr' space) =
>           space `isLocalSpaceOf` curSpace >>= \so ->
>           return (if so then ptr' else ptr)
>         copyNode _ _ ptr _ = return ptr
>         copyConstraint goalSpace curSpace (DisEq ptr) =
>           liftM DisEq (copy goalSpace curSpace ptr)

\end{verbatim}
Inside an encapsulated search, free variables of the search goal must
not be bound nor evaluated within the encapsulated search. Otherwise,
the program could become unsound. For instance, consider the program
\begin{verbatim}
  coin = 0
  coin = 1
  main = (x,map unpack (all (\y -> y =:= x))) where x = coin
\end{verbatim}
If \texttt{x} were evaluated in the local search space, either the
global choice point for the evaluation of \texttt{coin} would be lost
(because it occurs inside the encapsulated search), or the pair
\texttt{(0,[0,1])} would be computed. For that reason, all free
variables are wrapped in global application and global variable nodes
and the current search is suspended when a global application node
must be evaluated or a global variable node is matched. After the
application has been evaluated or the variable has been instantiated,
the global reference node is overwritten with a shallow copy of the
result or bound variable whose arguments are wrapped in global
application nodes. If the result of evaluating a global application is
an unbound logical variable, a global variable node is returned
instead.

\ToDo{Do not wrap atomic arguments at all and use global variable
  nodes for all arguments which are in head normal form already.}
\begin{verbatim}

> suspendSearch :: NodePtr -> Node -> Instruction -> Instruction
> suspendSearch ptr node next =
>   do
>     assertGlobalRef node
>     updateState (interruptThread next)
>     cont <- readState saveContinuation
>     space <- read'updateState saveSearchSpace
>     (goalApp,goalVar) <- read'updateState popSearchContext
>     updateState (pushCont (resumeSearch ptr goalApp goalVar cont space))
>     updateState initEnv
>     suspend ptr node
>   where assertGlobalRef (GlobalAppNode _ space) =
>           readState (isALocalSpace space) >>= \so ->
>           when so (fail "suspendSearch: global application is not global")
>         assertGlobalRef (GlobalVarNode _ space) =
>           readState (isALocalSpace space) >>= \so ->
>           when so (fail "suspendSearch: Global variable is not global")
>         assertGlobalRef _ = fail "suspendSearch: Not a global reference"
>         suspend ptr node@(GlobalAppNode ptr' space) =
>           readState (isALocalSpace space) >>= \so ->
>           if so then
>             updateState (setVar "x" ptr') >> enter "x"
>           else
>             suspendSearch ptr node (retNode ptr)
>         suspend ptr node@(GlobalVarNode ptr' space) =
>           readState (isALocalSpace space) >>= \so ->
>           if so then
>             updateState (setVar "x" ptr') >> switchRigid "x" [] retNode
>           else
>             suspendSearch ptr node (retNode ptr)

> resumeSearch ::
>     NodePtr -> NodePtr -> NodePtr -> ThreadQueue -> SearchSpace -> Instruction
> resumeSearch gptr goalApp goalVar cont space =
>   do
>     ptr <- read'updateState popNode
>     deref gptr >>= updateState . saveBinding gptr
>     deref ptr >>= globalNode ptr >>= updateNode gptr
>     space' <- read'updateState newSearchSpace
>     updateState (pushSearchContext goalApp goalVar space')
>     updateState (restoreSearchSpace space)
>     updateState (resumeContinuation cont)
>     switchContext
>   where globalNode ptr (CharNode _) = return (IndirNode ptr)
>         globalNode ptr (IntNode _) = return (IndirNode ptr)
>         globalNode ptr (FloatNode _) = return (IndirNode ptr)
>         globalNode _ (ConstructorNode t c ptrs) =
>           do
>             ptrs' <- globalArgs ptrs
>             ptr <- read'updateState (allocNode (ConstructorNode t c ptrs'))
>             return (IndirNode ptr)
>         globalNode ptr (VarNode _ _) =
>           readState curSpace >>= return . GlobalVarNode ptr
>         globalNode _ (ClosureNode f n code ptrs)
>           | length ptrs < n =
>               do
>                 ptrs' <- globalArgs ptrs
>                 ptr <-
>                   read'updateState (allocNode (ClosureNode f n code ptrs'))
>                 return (IndirNode ptr)
>         globalNode _ (IndirNode ptr) = deref ptr >>= globalNode ptr
>         globalNode ptr (SearchContinuation _ _ _ _) = return (IndirNode ptr)
>         globalNode _ (GlobalAppNode ptr space) =
>           return (GlobalAppNode ptr space)
>         globalNode _ (GlobalVarNode ptr space) =
>           return (GlobalVarNode ptr space)
>         globalNode _ _ = fail "resumeSearch: non-hnf result"

> globalArgs :: [NodePtr] -> MachStateT [NodePtr]
> globalArgs ptrs =
>   do
>     space <- readState curSpace
>     mapM (\ptr -> read'updateState (allocNode (GlobalAppNode ptr space))) ptrs

\end{verbatim}
\subsubsection{Monadic I/O Operations}
\begin{verbatim}

> unit :: MachStateT NodePtr
> unit = read'updateState (atom unitTag)

> getCharFunction,getLineFunction,putCharFunction,putStrFunction :: Function
> getCharFunction = ("getChar",getCharCode,1)
> getLineFunction = ("getLine",getLineCode,1)
> putCharFunction = ("putChar",putCharCode,2)
> putStrFunction = ("putStr",putStrCode,2)

> getCharCode :: Instruction
> getCharCode =
>   entry ["_"] $
>   do
>     c <- liftIO $ catch (liftM Just getChar) handleEOF
>     maybe (fail "End of file") allocChar c >>= retNode
>   where handleEOF e = if isEOFError e then return Nothing else ioError e

> getLineCode :: Instruction
> getLineCode =
>   entry ["_"] $
>   do
>     cs <- liftIO $ catch getLine handleEOF
>     mapM allocChar cs >>= list >>= retNode
>   where handleEOF e = if isEOFError e then return [] else ioError e

> putCharCode :: Instruction
> putCharCode =
>   entry ["c","_"]
>         (seqStmts "_c" (enter "c")
>                   (switchRigid "_c" [] (withChar "putChar" putCharIO)))
>   where putCharIO c = liftIO (putChar c) >> unit >>= retNode

> putStrCode :: Instruction
> putStrCode =
>   entry ["cs","_"]
>         (seqStmts "_cs" (enter "cs")
>           (switchRigid "_cs" [(nilTag,const (unit >>= retNode)),
>                               (consTag,putStrHead)]
>                        (const (fail "putStr: bad argument type!"))))
>   where putStrHead ptr = deref ptr >>= putStrNode
>         putStrNode (ConstructorNode _ _ [hd,tl]) =
>           do
>             updateState (setVar "c" hd)
>             updateState (setVar "cs" tl)
>             seqStmts "" (exec putCharFunction ["c","_"])
>                      (exec putStrFunction ["cs","_"])

> curryExitFunction :: Function
> curryExitFunction = ("curryExit",curryExitCode,2)

> curryExitCode :: Instruction
> curryExitCode =
>   entry ["i","_"]
>         (seqStmts "_i" (enter "i")
>            (switchRigid "_i" [] (withInt "curryExit" curryExitIO)))
>   where curryExitIO _ = return Nothing

> liftIO :: IO a -> MachStateT a
> liftIO = liftSt . liftErr

\end{verbatim}
\subsection{The Driver}
When the program finally stops, we have to construct a disjunctive
expression from the final graph. How this is done will be explained
below.

First we are going to describe how the machine is initialized. The
abstract machine can be operated in two modes: Either it reduces a
goal expression to normal form and displays the resulting disjunctive
expression on the standard output, or the goal expression is a monadic
expression which is simply reduced to normal form.

In the first case, a function that is the compiled form of the goal
expression with all free variables as its arguments is expected as
input. The task of the abstract machine therefore is to apply this
function to fresh variables and reduce this application to normal
form. Evaluation to normal form is achieved by unification of the
application with an unbound variable. Thus, our program is equivalent
to the expression
\begin{verbatim}
  x =:= goal where x free
\end{verbatim}
When the machine finally stops, the current value of the goal is
printed using the \texttt{print\_result} function. If there are any
alternative computations available, the abstract machine will be
started again at the alternative continuation address.

In the second case, the goal is a monadic expression, i.e., a function
that takes the initial state of the world as input and returns a
result together with the final state of the world. As the world is
already maintained implicitly by the abstract machine, we simply pass
the nullary tuple as input argument and expect the monadic function to
return just the result. Actually, this result is discarded.

To handle both modes of operation, we provide two entry points for the
abstract machine: The function \texttt{start} reduces a goal
expression and displays the resulting disjunctive expressions, whereas
\texttt{startIO} reduces a monadic expression. We make use of the
predefined function \texttt{@} to apply the goal expression to the
fake world.
\begin{verbatim}

> start :: Function -> [String] -> ErrorT IO ShowS
> start (f,code,n) fvNames
>   | nVars <= n = callSt driver initialState
>   | otherwise = fail "too many arguments for goal"
>   where nVars = length fvNames
>         driver =
>           do
>             updateState newThread
>             (fv:fvs) <- allocVariables (nVars + 1)
>             goal <- allocGoal (f,code,n) fvs
>             updateState (pushNodes [fv,goal])
>             unifyCode >>= showResults 0 (zip fvNames fvs) goal
>         initialState =
>           State{ tid = 0,
>                  env = emptyEnv,
>                  ds = [],
>                  rs = [],
>                  rq = [],
>                  hp = 0,
>                  bp = [],
>                  tp = [],
>                  ct = 0,
>                  sc = GlobalContext,
>                  ss = GlobalSpace }
>         showResults n freeVars goal Nothing
>           | n == 0 = fail "No solution"
>           | otherwise = return (showChar '\n')
>         showResults n freeVars goal _ =
>           do
>             disjunct <- browse freeVars goal
>             disjuncts <- failAndBacktrack >>= showResults (n+1) freeVars goal
>             return (sep . disjunct . disjuncts)
>           where sep = if n > 0 then showString " | " else id
>         allocGoal (f,code,n) vs
>           | length vs < n = allocClosure (f,code,n) vs
>           | otherwise = allocLazy (f,code,n) vs

> startIO :: Function -> ErrorT IO ShowS
> startIO main = callSt driver initialState
>   where driver =
>           do
>             updateState newThread
>             allocMain main >>= updateState . setVar "m"
>             unit >>= updateState . setVar "_"
>             exec applyFunction ["m","_"] >>= catchError
>         initialState =
>           State{ tid = 0,
>                  env = emptyEnv,
>                  ds = [],
>                  rs = [],
>                  rq = [],
>                  hp = 0,
>                  bp = [],
>                  tp = [],
>                  ct = 0,
>                  sc = IOContext,
>                  ss = GlobalSpace }
>         catchError Nothing = fail "Failed"
>         catchError (Just state)
>           | tid state == 0 && null (rs state) = return id
>           | otherwise = fail "Suspended"
>         allocMain (f,code,n)
>           | n == 0 = allocLazy (f,code,n) []
>           | otherwise = allocClosure (f,code,n) []

\end{verbatim}
\ToDo{Integrate the \texttt{start} function into \texttt{startIO} and
give the program a chance to compute all results of the goal and print
them. Should the driver programs be moved into the loader?}

\subsection{``Micro-code''}
\subsubsection{Wrapper Functions}
The following functions are used to convert the ``micro code'' state
transformer functions into state monads.
\begin{verbatim}

> readState :: Monad m => (State -> m a) -> StateT State m a
> readState f = StateT (\state -> f state >>= \x -> return (x, state))

> updateState :: Monad m => (State -> m State) -> StateT State m ()
> updateState f = StateT (\state -> f state >>= \state' -> return ((), state'))

> read'updateState :: Monad m => (State -> m (a, State)) -> StateT State m a
> read'updateState = StateT

\end{verbatim}
\input{MachNode.lhs} % \subsubsection{Nodes}
\input{MachStack.lhs} % \subsubsection{Data Stack Management}
\input{MachEnviron.lhs} %  \subsubsection{Environment Management}
\input{MachChoice.lhs} % \subsubsection{Choicepoints and Backtracking}
\input{MachSpace.lhs} % \subsection{Local Search Spaces}
\input{MachThreads.lhs} % \subsubsection{Thread Management}

\input{MachResult.lhs} % \subsection{Building a Disjunctive Expression}

\input{MachLoader.lhs} % \subsection{Loading a Program}
