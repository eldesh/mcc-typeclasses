% -*- LaTeX -*-
% $Id: MachLoader.lhs 3003 2010-08-30 19:42:53Z wlux $
%
% Copyright (c) 1998-2009, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{MachLoader.lhs}
\subsection{Loading Programs}
The purpose of the loader is to convert an abstract machine program
into a state transformer monad and to construct the global constructor
and function environments from the declarations of the program. This
process has to translate every abstract machine statement into the
corresponding transformer function and also has to resolve references
to the functions.
\begin{verbatim}

> module MachLoader(Instrument, ConstrEnv, FunEnv,
>                   loadModule,function, initConstrEnv,initFunEnv,
>                   noTrace,traceInstr,traceStack,dumpPtr,dumpArgs) where
> import Cam
> import MachTypes
> import MachInterp
> import Char
> import List
> import Env
> import Monad
> import Combined
> import Utils

> type ConstrEnv = Env String NodeTag
> type FunEnv = Env String Function
> type PrimEnv = Env String Primitive

> loadModule :: Maybe Instrument -> ConstrEnv -> FunEnv -> Module
>            -> (ConstrEnv,FunEnv)
> loadModule instrumentOpt cEnv fEnv cam = (cEnv',fEnv'')
>   where (_,ds,fs) = splitCam cam
>         cs = concatMap constrs ds
>         cEnv' = foldr bindConstr cEnv cs
>         fEnv' = foldr bindConstrFun fEnv cs
>         fEnv'' = translate instrumentOpt cEnv' fEnv' fs

> constrs :: (Name,[Name],[ConstrDecl]) -> [(ConstrDecl,Int)]
> constrs (_,_,cs) = zip cs [0..]

> function :: String -> FunEnv -> Maybe Function
> function = lookupEnv

\end{verbatim}
As part of the translation of statements, we provide the option to
instrument the code, e.g., for tracing purposes. The optional
instrumenting function is inserted before each statement. Note the use
of a circular environment to lookup function names. This is necessary
in order to allow mutual recursion between functions.
\begin{verbatim}

> type Instrument = Stmt -> Instruction -> Instruction

> translate :: Maybe Instrument -> ConstrEnv -> FunEnv -> [(Name,[Name],Stmt)]
>          -> FunEnv
> translate instrument cEnv fEnv fs = fEnv'
>   where fEnv' = foldr (bindFun . translFun instrument cEnv fEnv') fEnv fs

> translFun :: Maybe Instrument -> ConstrEnv -> FunEnv -> (Name,[Name],Stmt)
>           -> (Name,Int,Instruction)
> translFun instrument cEnv fEnv (f,vs,st) =
>   (f,length vs,entry (map show vs) (transl st))
>   where transl = maybe translStmt translInstrumented instrument
>         translInstrumented instrument st = instrument st (translStmt st)
>         translStmt (Return e) = returnNode (translExpr Nothing e)
>         translStmt (Eval v) = enter (show v)
>         translStmt (Exec f vs) = exec (lookupFun f fEnv) (map show vs)
>         translStmt (CCall _ _ cc) = translCCall cc
>         translStmt (Seq (v :<- st1) st2) =
>           seqStmts (show v) (transl st1) (transl st2)
>         translStmt (Let ds st) = letNodes ns (transl st)
>           where ns = [(show v,translExpr (Just v) n) | Bind v n <- ds]
>         translStmt (Switch rf v cases) =
>           uncurry (switch rf (show v)) (translCases cases)
>           where switch Rigid = switchRigid
>                 switch Flex = switchFlex
>         translStmt (Choice alts) = choice (map transl alts)
>         translCCall (StaticCall f vs) =
>           cCall (lookupPrim f primEnv) (map (show . snd) vs)
>         translCCall (DynamicCall _ _) =
>           error "Foreign dynamic calls are not supported"
>         translCCall (StaticAddr _) =
>           error "Foreign static addresses are not supported"
>         translCases cases =
>           (map translCase nonDflts,
>            head (map (snd . translCase) dflts ++ [const failAndBacktrack]))
>           where (dflts,nonDflts) = partition isDefault cases
>                 isDefault (Case DefaultCase _) = True
>                 isDefault _ = False
>         translCase (Case t st) =
>           (caseTag cEnv t,bindArgs (translPattern t) (transl st))
>         translExpr _ (Lit c) = translLiteral c
>         translExpr _ (Constr c vs) =
>           initConstr (lookupConstr c cEnv) (map show vs)
>         translExpr _ (Papp f vs) =
>           initClosure (lookupFun f fEnv) (map show vs)
>         translExpr _ (Closure f vs) =
>           initClosure (lookupFun f fEnv) (map show vs)
>         translExpr _ (Lazy f vs) = initLazy (lookupFun f fEnv) (map show vs)
>         translExpr _ Free = initFree
>         translExpr v (Var v')
>           | v == Just v' = initQueueMe
>           | otherwise = initIndir (show v')
>         translLiteral (Char c) = initChar c
>         translLiteral (Int i) = initInt i
>         translLiteral (Integer i) = initInt i
>         translLiteral (Float f) = initFloat f
>         translPattern (LitCase _) = bindLiteral
>         translPattern (ConstrCase _ vs) = bindData (map show vs)
>         translPattern DefaultCase = bindLiteral

\end{verbatim}
A few simple instrumentation functions are given here. The function
\texttt{noTrace} just performs no action, \texttt{traceInstr} displays
every statement before it is executed. A little bit more output
results from the function \texttt{traceStack} which displays the
contents of the data stack, the environment variables, and the
variables from the update stack in addition to the statement. The
amount of information displayed for each node can be controlled by an
argument function passed to \texttt{traceStack}.
\begin{verbatim}

> noTrace :: Instrument
> noTrace i next = next

> traceInstr :: Instrument
> traceInstr i next = readState (liftErr . dumpInstr i) >> next

> traceStack :: (NodePtr -> IO ()) -> Instrument
> traceStack dumpNode i next =
>   readState (liftErr . dumpStack dumpNode i) >> next

> dumpInstr :: Stmt -> State -> IO ()
> dumpInstr st state = dumpThreadId state >> putStrLn (" " ++ show st)

> dumpThreadId :: State -> IO ()
> dumpThreadId state = putStr ("[" ++ show (tid state) ++ spaceId state ++ "]")
>   where spaceId state =
>           case ss state of
>             GlobalSpace -> ""
>             LocalSpace id _ _ _ _ _ -> "/" ++ show id

> dumpStack :: (NodePtr -> IO ()) -> Stmt -> State -> IO ()
> dumpStack dumpNode st state =
>   do
>     dumpThreadId state
>     dumpList dumpNode '[' (ds state) ']'
>     dumpEnv (envToList (env state))
>     putStrLn ""
>     putStrLn (" " ++ show st)
>   where dumpEnv env
>           | null env = return ()
>           | otherwise = dumpList dumpEnvVar '{' env '}'
>         dumpEnvVar (v,ptr) = do putStr v; putStr "="; dumpNode ptr
>         dumpList dump lb xs rb =
>           do
>             putChar lb
>             sequence_ (intersperse (putStr ", ") (map dump xs))
>             putChar rb

> dumpPtr :: Int -> NodePtr -> IO ()
> dumpPtr d (Ptr adr ref)
>   | d < 0 = putStr "..."
>   | otherwise = readRef ref >>= dumpNode d adr
>   where dumpNode d adr (CharNode c) = putStr (show c)
>         dumpNode d adr (IntNode i) = putStr (show i)
>         dumpNode d adr (FloatNode f) = putStr (show f)
>         dumpNode d adr (ConstructorNode _ name args) =
>           putStr ("data@" ++ show adr) >>
>           when (d > 0)
>                (putStr ('(' : name) >> dumpArgs (d-1) args >> putChar ')')
>         dumpNode d adr (VarNode cs wq) = putStr ("var@" ++ show adr)
>         dumpNode d adr (ClosureNode name _ _ args) =
>           putStr ("clos@" ++ show adr) >>
>           when (d > 0)
>                (putStr ('(' : name) >> dumpArgs (d-1) args >> putChar ')')
>         dumpNode d adr (LazyNode name _ _ args) =
>           putStr ("lazy@" ++ show adr) >>
>           when (d > 0)
>                (putStr ('(' : name) >> dumpArgs (d-1) args >> putChar ')')
>         dumpNode d adr (QueueMeNode wq) = putStr ("lock@" ++ show adr)
>         dumpNode d adr (IndirNode ptr) =
>           putStr ("indir@" ++ show adr) >>
>           when (d > 0) (putChar '(' >> dumpPtr (d-1) ptr >> putChar ')')
>         dumpNode d adr (GlobalAppNode ptr space) =
>           putStr ("gapp@" ++ show adr ++ showSpace space) >>
>           when (d > 0) (putChar '(' >> dumpPtr (d-1) ptr >> putChar ')')
>         dumpNode d adr (GlobalVarNode ptr space) =
>           putStr ("gvar@" ++ show adr ++ showSpace space) >>
>           when (d > 0) (putChar '(' >> dumpPtr (d-1) ptr >> putChar ')')
>         dumpNode d adr (SearchContinuation _ _ _ _) =
>           putStr ("cont@" ++ show adr)
>         showSpace GlobalSpace = ""
>         showSpace (LocalSpace id _ _ _ _ _) = "/" ++ show id

> dumpArgs :: Int -> [NodePtr] -> IO ()
> dumpArgs d [] = return ()
> dumpArgs d args
>   | d <= 0 = putStr " ..."
>   | otherwise = mapM_ (dumpArg d) args
>   where dumpArg d arg = putChar ' ' >> dumpPtr d arg

\end{verbatim}
Here is the implementation of the environments mapping constructor
names to node tags and function names to function triples.
\begin{verbatim}

> initConstrEnv :: ConstrEnv
> initConstrEnv =
>   foldr bindTag emptyEnv [nilTag,consTag,unitTag,successTag]
>   where bindTag (ConstructorTag t c n) = bindEnv c (ConstructorTag t c n)

> bindConstr :: (ConstrDecl,Int) -> ConstrEnv -> ConstrEnv
> bindConstr (ConstrDecl c tys,t) =
>   bindEnv c' (ConstructorTag t c' (length tys))
>   where c' = demangle c

> lookupConstr :: Name -> ConstrEnv -> NodeTag
> lookupConstr c env =
>   case lookupEnv c' env of
>     Just x -> x
>     Nothing
>       | isTupleName c' -> ConstructorTag 0 c' (length c' - 1)
>       | otherwise -> error ("Undefined constructor: " ++ c')
>   where c' = demangle c

> tagWithArity :: Name -> Int -> ConstrEnv -> NodeTag
> tagWithArity c n env
>   | n == n' = ConstructorTag t c' n'
>   | otherwise =
>       error ("Constructor " ++ demangle c ++ " is used with " ++ 
>              showArguments n ++ " but requires " ++ show n')
>   where ConstructorTag t c' n' = lookupConstr c env
>         showArguments n = show n ++ " argument" ++ if n == 1 then "" else "s"

> caseTag :: ConstrEnv -> Tag -> NodeTag
> caseTag env (ConstrCase c vs) = tagWithArity c (length vs) env
> caseTag _ (LitCase c) = litTag c

> litTag :: Literal -> NodeTag
> litTag (Char c) = CharTag c
> litTag (Int i) = IntTag i
> litTag (Integer i) = IntTag i
> litTag (Float f) = FloatTag f

> initFunEnv :: FunEnv
> initFunEnv = foldr bindFun emptyEnv [
>       consFunction,failedFunction,successFunction,concConjFunction,
>       seqFunction,ensureNotFreeFunction,tryFunction,
>       equalFunction,compareFunction,unifyFunction,diseqFunction,
>       addIntFunction,subIntFunction,multIntFunction,
>       quotIntFunction,remIntFunction,divIntFunction,modIntFunction,
>       ordFunction,chrFunction,
>       addFloatFunction,subFloatFunction,multFloatFunction,divFloatFunction,
>       floatFromIntFunction,roundFloatFunction,truncateFloatFunction,
>       pbUpdateFunction,pbReturnFunction,
>       doneFunction,returnFunction,bind'Function,bindFunction,
>       getCharFunction,getLineFunction,putCharFunction,putStrFunction,
>       unsafePerformFunction,curryExitFunction
>     ]
>   where bindFun fn@(name,_,_) = bindEnv name fn

> bindFun :: (Name,Int,Instruction) -> FunEnv -> FunEnv
> bindFun (f,n,code) = bindEnv f' (f',code,n)
>   where f' = demangle f

> bindConstrFun :: (ConstrDecl,Int) -> FunEnv -> FunEnv
> bindConstrFun (ConstrDecl c tys,t) =
>   bindEnv c' (constrFunction t c' (length tys))
>   where c' = demangle c

> lookupFun :: Name -> FunEnv -> Function
> lookupFun f fEnv =
>   case lookupEnv f' fEnv of
>     Just f -> f
>     Nothing
>       | isApName f' -> applyFunctions !! (apArity f' - 1)
>       | isTupleName f' -> tupleFunctions !! (tupleArity f')
>       | otherwise -> error ("Undefined function: " ++ f')
>   where f' = demangle f
>         isApName ('@':cs) = all isDigit cs
>         isApName _ = False
>         apArity ('@':cs) = if null cs then 1 else read cs
>         tupleArity ('P':'r':'e':'l':'u':'d':'e':'.':'(':cs) = length cs

\end{verbatim}
The environment holding the \verb|ccall|able primitives is fixed.
\begin{verbatim}

> primEnv :: PrimEnv
> primEnv = foldr bindPrim emptyEnv [
>       ordPrimitive, chrPrimitive,
>       addIntPrimitive, subIntPrimitive, mulIntPrimitive,
>       quotIntPrimitive, remIntPrimitive, divIntPrimitive, modIntPrimitive,
>       addFloatPrimitive, subFloatPrimitive, mulFloatPrimitive,
>       divFloatPrimitive, floatPrimitive, truncPrimitive, roundPrimitive
>     ]
>   where bindPrim fn@(name,_) = bindEnv name fn

> lookupPrim :: String -> PrimEnv -> Primitive
> lookupPrim f env =
>   case lookupEnv f env of
>     Just prim -> prim
>     Nothing -> error ("Undefined ccall primitive: " ++ f)

\end{verbatim}
