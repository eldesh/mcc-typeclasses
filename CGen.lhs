% -*- LaTeX -*-
% $Id: CGen.lhs 2303 2007-06-20 07:22:47Z wlux $
%
% Copyright (c) 1998-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CGen.lhs}
\section{Generating C Code}
\begin{verbatim}

> module CGen(genMain,genModule) where
> import Cam
> import CCode
> import CPS
> import CElim
> import Char
> import List
> import Map
> import Maybe
> import Set
> import Utils

\end{verbatim}
\subsection{Start-up Code}
The function \texttt{genMain} generates the start-up code for a Curry
program. It defines the main function of the program and also the
global variables that hold the default sizes of the heap, the stack,
and the trail. The main function first initializes the runtime system
by calling \verb|curry_init|, then executes the main function of the
Curry program by invoking \verb|curry_exec| for a monadic goal and
\verb|curry_eval| for a non-monadic goal, respectively, and finally
calls \verb|curry_terminate|, which eventually prints the statistics
for the run. In case of a non-monadic goal, the main function also
defines the array holding the names of the goal's free variables.
\begin{verbatim}

> genMain :: Name -> Maybe [String] -> [CTopDecl]
> genMain f fvs = CppInclude "curry.h" : defaultVars ++ mainFunction f fvs

> defaultVars :: [CTopDecl]
> defaultVars =
>   [CVarDef CPublic ty v (CInit (CExpr (defaultValue v))) | (ty,v) <- vars]
>   where vars = [
>             (ulongType, "heapsize"),
>             (uintType,  "stacksize"),
>             (uintType,  "trailsize"),
>             (intType,   "print_fail"),
>             (intType,   "do_trace"),
>             (intType,   "show_stats")
>           ]
>         defaultValue v = "DEFAULT_" ++ map toUpper v

> mainFunction :: Name -> Maybe [String] -> [CTopDecl]
> mainFunction f fvs =
>   [CMainFunc "main" ["argc","argv"]
>     (maybe [] (return . fvDecl "fv_names") fvs ++
>      [procCall "curry_init" ["&argc","argv"],
>       CLocalVar intType "rc"
>         (Just (curry_main fvs (nodeInfo f) "fv_names" ["argc","argv"])),
>       procCall "curry_terminate" [],
>       procCall "exit" ["rc"],
>       CReturn (CInt 0)])]
>   where fvDecl v vs =
>           CStaticArray (CPointerType (CConstType "char")) v
>                        (map CInit (map CString vs ++ [CNull]))
>         curry_main (Just _) = curry_eval
>         curry_main Nothing = const . curry_exec
>         curry_exec g args = CFunCall "curry_exec" (addr g : map CExpr args)
>         curry_eval g v args =
>           CFunCall "curry_eval" (addr g : map CExpr (v:args))

\end{verbatim}
\subsection{Modules}
The C code for a module is divided into code generated for the data
type declarations and code generated for the function definitions of
the module. Code generation is complicated by a few special cases that
need to be handled. In particular, the compiler must provide
definitions for those tuples that are used in the module and for the
functions \texttt{@}$_n$ that implement applications of a higher order
variable to $n$ arguments.\footnote{Only functions with $n\geq2$ are
generated. Instead of \texttt{@}$_1$, the function \texttt{@}, which
is implemented in the runtime system, is used.} These functions cannot
be predefined because there are no upper limits on the arity of a
tuple or application. Since these functions may be added in each
module, they must be declared as private -- i.e., \verb|static| --
functions.

\ToDo{The runtime system should preallocate tuple descriptors up to a
reasonable size (e.g., 10). Thus the compiler only has to create
private descriptors if a module uses a tuple with a higher arity.}

In addition, the code generator preallocates the nodes for literal
constants globally. In fact, it preallocates all constants, but this
is done independently. Constant constructors are defined together with
their node info and other constants are allocated separately for every
function because there is not much chance for them to be shared.
\begin{verbatim}

> genModule :: [Decl] -> Module -> CFile
> genModule impDs cam =
>   map CppInclude (nub ("curry.h" : [h | CCall (Just h) _ _ <- sts])) ++
>   genTypes impDs ds sts ns ++
>   genFunctions ds fs sts ns
>   where (_,ds,fs) = splitCam cam
>         (sts0,sts) = foldr linStmts ([],[]) (map thd3 fs)
>         ns = nodes sts ++ letNodes sts0 ++ ccallNodes sts ++ flexNodes sts

> linStmts :: Stmt -> ([Stmt0],[Stmt]) -> ([Stmt0],[Stmt])
> linStmts st sts = addStmt st (linStmts' st sts)
>   where addStmt st ~(sts0,sts) = (sts0,st:sts)

> linStmts' :: Stmt -> ([Stmt0],[Stmt]) -> ([Stmt0],[Stmt])
> linStmts' (Return _) sts = sts
> linStmts' (Enter _) sts = sts
> linStmts' (Exec _ _) sts = sts
> linStmts' (CCall _ _ _) sts = sts
> linStmts' (Seq st1 st2) sts = addStmt st1 $ linStmts0 st1 $ linStmts st2 sts
>   where addStmt st ~(sts0,sts) = (st:sts0,sts)
>         linStmts0 (_ :<- st) sts = linStmts st sts
>         linStmts0 _ sts = sts
> linStmts' (Switch rf x cs) sts = foldr linStmts sts [st | Case _ st <- cs]
> linStmts' (Choices sts) sts' = foldr linStmts sts' sts

> switchTags :: [Stmt] -> [(Name,Int)]
> switchTags sts =
>   [(c,length vs) | Switch _ _ cs <- sts, Case (ConstrCase c vs) _ <- cs]

> nodes :: [Stmt] -> [Expr]
> nodes sts = [n | Return n <- sts]

> letNodes :: [Stmt0] -> [Expr]
> letNodes sts0 = [n | Let bds <- sts0, Bind _ n <- bds]

> ccallNodes :: [Stmt] -> [Expr]
> ccallNodes sts
>   | TypeBool `elem` [ty | CCall _ (Just ty) _ <- sts] =
>       [Constr prelTrue [],Constr prelFalse []]
>   | otherwise = []

> flexNodes :: [Stmt] -> [Expr]
> flexNodes sts = [node t | Switch Flex _ cs <- sts, Case t _ <- cs]
>   where node (LitCase l) = Lit l
>         node (ConstrCase c vs) = Constr c vs

\end{verbatim}
\subsection{Data Types and Constants}
For every data type, the compiler defines an enumeration that assigns
tag numbers to its data constructors. Normally, tags starting at zero
are assigned from left to right to the constructors of each type.
However, in order to distinguish constructors of existentially
quantified types, those constructors are assigned negative tag values
starting at $-1$. The \verb|enum| declarations are not strictly
necessary, but simplify the code generator because it does not need to
determine the tag value of a constructor when it is used.

In addition to the tag enumerations, the compiler also defines node
info structures for every data constructor and preallocates constant
constructors and literal constants. Character constants with codes
below 256 are allocated in a table defined by the runtime system.
Integer constants need to be allocated only if they cannot be
represented in $n-1$ bits where $n$ is the bit size of the target
machine. The generated code uses the preprocessor macro
\texttt{is\_large\_int} defined in the runtime system (see
Sect.~\ref{sec:heap}) in order to determine whether allocation is
necessary. Note that this macro always returns true if the system was
configured with the \texttt{--disable-pointer-tags} configuration
option.
\begin{verbatim}

> genTypes :: [Decl] -> [(Name,[Name],[ConstrDecl])] -> [Stmt] -> [Expr]
>          -> [CTopDecl]
> genTypes impDs ds sts ns =
>   -- imported data constructors
>   [tagDecl t vs cs | DataDecl t vs cs <- impDs, any (`conElem` usedTs) cs] ++
>   [dataDecl c | DataDecl _ _ cs <- impDs, c <- cs, c `conElem` usedCs] ++
>   -- (private) tuple constructors
>   map (tupleTagDecl . fst) (nub (usedTts ++ usedTcs)) ++
>   concatMap (dataDef CPrivate . uncurry tupleConstr) usedTcs ++
>   -- local data declarations
>   [tagDecl t vs cs | (t,vs,cs) <- ds] ++
>   concat [dataDecl c : dataDef CPublic c | cs <- map thd3 ds, c <- cs] ++
>   -- literal constants
>   literals [c | Lit c <- ns]
>   where constrs = [(c,length vs) | Constr c vs <- ns]
>         (usedTts,usedTs) = partition (isTuple . fst) (nub (switchTags sts))
>         (usedTcs',usedCs) = partition (isTuple . fst) (nub constrs)
>         usedTcs = nub (usedTcs' ++ usedTfs)
>         usedTfs = [(f,tupleArity f) | Papp f _ <- ns, isTuple f]
>         conElem c = (constr c `elem`)

> constr :: ConstrDecl -> (Name,Int)
> constr (ConstrDecl c tys) = (c,length tys)

> tupleConstr :: Name -> Int -> ConstrDecl
> tupleConstr c n = ConstrDecl c (map TypeVar vs)
>   where vs = [Name ('a' : show i) | i <- [1..n]]

> tagDecl :: Name -> [Name] -> [ConstrDecl] -> CTopDecl
> tagDecl _ vs cs =
>   CEnumDecl [CConst (dataTag c) (Just n)
>             | (ConstrDecl c _,n) <- zip cs tags, c /= Name "_"]
>   where tags
>           | any hasExistType cs = [-1,-2..]
>           | otherwise = [0..]
>         hasExistType (ConstrDecl _ tys) = any hasExistVar tys
>         hasExistVar (TypeVar v) = v `notElem` vs
>         hasExistVar (TypeApp _ tys) = any hasExistVar tys
>         hasExistVar (TypeArr ty1 ty2) = hasExistVar ty1 || hasExistVar ty2

> tupleTagDecl :: Name -> CTopDecl
> tupleTagDecl c = CEnumDecl [CConst (dataTag c) (Just 0)]

> dataDecl :: ConstrDecl -> CTopDecl
> dataDecl (ConstrDecl c tys)
>   | null tys = CExternVarDecl nodeInfoConstPtrType (constNode c)
>   | otherwise = CExternVarDecl nodeInfoType (nodeInfo c)

> dataDef :: CVisibility -> ConstrDecl -> [CTopDecl]
> dataDef vb (ConstrDecl c tys)
>   | null tys =
>       [CVarDef CPrivate nodeInfoType (nodeInfo c) nodeinfo,
>        CVarDef vb nodeInfoConstPtrType (constNode c)
>                (CInit (addr (nodeInfo c)))]
>   | otherwise = [CVarDef vb nodeInfoType (nodeInfo c) nodeinfo]
>   where nodeinfo = CStruct (map CInit nodeinfo')
>         nodeinfo' =
>           [CExpr "CAPP_KIND",CExpr (dataTag c),closureNodeSize (length tys),
>            gcPointerTable,CString name,CExpr "eval_whnf",noApply,noEntry,
>            notFinalized]
>         name = snd $ splitQualified $ demangle c

> literals :: [Literal] -> [CTopDecl]
> literals cs =
>   map charConstant (nub [c | Char c <- cs, ord c >= 0x100]) ++
>   map intConstant (nub [i | Int i <- cs]) ++
>   map floatConstant (nub [f | Float f <- cs])

> charConstant :: Char -> CTopDecl
> charConstant c =
>   CVarDef CPrivate (CConstType "struct char_node") (constChar c)
>           (CStruct $ map CInit [addr "char_info",CInt (ord c)])

> intConstant :: Int -> CTopDecl
> intConstant i =
>   CppCondDecls (CFunCall "is_large_int" [CInt i])
>     [CVarDef CPrivate (CConstType "struct int_node") (constInt i)
>              (CStruct $ map CInit [addr "int_info",CInt i]),
>      CppDefine (constInt i) (constRef (constInt i))]
>     [CppDefine (constInt i) (CFunCall "tag_int" [CInt i])]

> floatConstant :: Double -> CTopDecl
> floatConstant f =
>   CVarDef CPrivate (CConstType "struct float_node") (constFloat f)
>           (CStruct $ map CInit [addr "float_info",fval f])
>   where fval f
>           | isNaN f = error "internalError: NaN literal in CGen.floatConstant"
>           | isInfinite f = CExpr (withSign f "1e500")
>           | otherwise = CFloat f
>         withSign f cs = if f < 0 then '-' : cs else cs

> gcPointerTable, notFinalized :: CExpr
> gcPointerTable = CNull
> notFinalized = CNull
> noApply = CNull
> noEntry = CNull
> noName = CNull

\end{verbatim}
\subsection{Functions}
Besides the code for all defined functions, the compiler also
generates node descriptors for them. These descriptors are used for
partial applications of the functions and for (updatable and
non-updatable) lazy application nodes. In addition, the compiler
introduces auxiliary functions that instantiate unbound variables with
literals and data constructors, respectively, and functions that
implement partial applications of data constructors including tuple
constructors used in the current module. Furthermore, the code for
those functions \texttt{@}$_n$, which are used in the current module,
is generated.
\begin{verbatim}

> genFunctions :: [(Name,[Name],[ConstrDecl])] -> [(Name,[Name],Stmt)]
>              -> [Stmt] -> [Expr] -> [CTopDecl]
> genFunctions ds fs sts ns =
>   -- imported functions
>   map (instEntryDecl CPublic) (nonLocalData (map fst flexData)) ++
>   map (entryDecl CPublic) (nonLocal call) ++
>   map pappDecl (nonLocal papp) ++
>   map evalDecl (nonLocal clos) ++
>   map lazyDecl (nonLocal lazy) ++
>   map fun0Decl (nonLocal fun0) ++
>   -- (private) closure and suspend node evaluation entry points
>   concat [[applyEntryDecl m n,applyFunction m n] | n <- pappArities,
>                                                    m <- [0..n-1]] ++
>   concat [[evalEntryDecl n,evalFunction n] | n <- closArities] ++
>   concat [[lazyEntryDecl n,lazyFunction n] | n <- lazyArities] ++
>   -- instantiation functions for data constructors
>   map (instEntryDecl CPublic . fst) cs ++
>   [instFunction CPublic c n | (c,n) <- cs] ++
>   -- (private) instantiation functions for literals
>   map litInstEntryDecl flexLits ++
>   map litInstFunction flexLits ++
>   -- (private) instantiation functions for tuples
>   map (instEntryDecl CPrivate . fst) flexTuples ++
>   [instFunction CPrivate c n | (c,n) <- flexTuples] ++
>   -- (private) @ functions
>   [entryDecl CPrivate (apName n) | n <- [3..maxApArity]] ++
>   concat [evalDef CPrivate f n | f <- apClos, let n = apArity f, n > 2] ++
>   concat [lazyDef CPrivate f n | f <- apLazy, let n = apArity f, n > 2] ++
>   concat [apFunction (apName n) n | n <- [3..maxApArity]] ++
>   -- (private) auxiliary functions for partial applications of tuples
>   map (entryDecl CPrivate) tuplePapp ++
>   concat [pappDef CPrivate f (tupleArity f) | f <- tuplePapp] ++
>   concat [fun0Def CPrivate f (tupleArity f) | f <- tupleFun0] ++
>   concat [conFunction CPrivate f (tupleArity f) | f <- tuplePapp] ++
>   -- auxiliary functions for partial applications of data constructors
>   map (entryDecl CPublic . fst) cs ++
>   concat [pappDef CPublic c n | (c,n) <- cs, n > 0] ++
>   concat [fun0Def CPublic c n | (c,n) <- cs, n > 0] ++
>   concat [conFunction CPublic c n | (c,n) <- cs, n > 0] ++
>   -- local function declarations
>   [entryDecl (public f) f | (f,_,_) <- fs] ++
>   concat [pappDef (public f) f n | (f,n) <- papp', n > 0] ++
>   concat [evalDef (public f) f n | (f,n) <- clos'] ++
>   concat [lazyDef (public f) f n | (f,n) <- lazy'] ++
>   concat [fun0Def (public f) f n | (f,n) <- fun0'] ++
>   concat [function (public f) f vs st | (f,vs,st) <- fs]
>   where nonLocal = filter (`notElem` map fst3 fs)
>         nonLocalData = filter (`notElem` map fst cs)
>         (tuplePapp,papp) = partition isTuple (nub [f | Papp f _ <- ns])
>         (apCall,call) = partition isAp (nub [f | Exec f _ <- sts])
>         (apClos,clos) = partition isAp (nub [f | Closure f _ <- ns])
>         (apLazy,lazy) = partition isAp (nub [f | Lazy f _ <- ns])
>         (tupleFun0,fun0) =
>           partition isTuple
>                     (nub ([f | Papp f [] <- ns] ++ [f | Closure f [] <- ns]))
>         maxApArity = maximum (0 : map apArity (apCall ++ apClos ++ apLazy))
>         cs = [constr c | c <- concatMap thd3 ds]
>         fs' = [(f,n) | (f,vs,_) <- fs, let n = length vs, (f,n) `notElem` cs]
>         papp' = filter (used papp . fst) fs'
>         clos' = filter (used clos . fst) fs'
>         lazy' = filter (used lazy . fst) fs'
>         fun0' = filter (used fun0 . fst) fs'
>         pappArities =
>           nub (map snd cs ++ map tupleArity tuplePapp ++ map snd papp')
>         closArities = nub (filter (> 2) (map apArity apClos) ++ map snd clos')
>         lazyArities = nub (filter (> 2) (map apArity apLazy) ++ map snd lazy')
>         ts = [t | Switch Flex _ cs <- sts, Case t _ <- cs]
>         flexLits = nub [l | LitCase l <- ts]
>         (flexTuples,flexData) =
>           partition (isTuple . fst)
>                     (nub [(c,length vs) | ConstrCase c vs <- ts])
>         used fs f = isPublic f || f `elem` fs
>         public f = if isPublic f then CPublic else CPrivate

> entryDecl :: CVisibility -> Name -> CTopDecl
> entryDecl vb f = CFuncDecl vb (cName f)

> applyEntryDecl :: Int -> Int -> CTopDecl
> applyEntryDecl m n = CFuncDecl CPrivate (applyFunc m n)

> evalEntryDecl :: Int -> CTopDecl
> evalEntryDecl n = CFuncDecl CPrivate (evalFunc n)

> lazyEntryDecl :: Int -> CTopDecl
> lazyEntryDecl n = CFuncDecl CPrivate (lazyFunc n)

> instEntryDecl :: CVisibility -> Name -> CTopDecl
> instEntryDecl vb c = CFuncDecl vb (instFunc c)

> litInstEntryDecl :: Literal -> CTopDecl
> litInstEntryDecl l = CFuncDecl CPrivate (litInstFunc l)

> pappDecl :: Name -> CTopDecl
> pappDecl f = CExternArrayDecl nodeInfoType (pappInfoTable f)

> evalDecl :: Name -> CTopDecl
> evalDecl f = CExternVarDecl nodeInfoType (nodeInfo f)

> lazyDecl :: Name -> CTopDecl
> lazyDecl f = CExternArrayDecl nodeInfoType (lazyInfoTable f)

> fun0Decl :: Name -> CTopDecl
> fun0Decl f = CExternVarDecl (CConstType "struct closure_node") (constFunc f)

> pappDef :: CVisibility -> Name -> Int -> [CTopDecl]
> pappDef vb f n =
>   [pappDecl f | vb == CPublic] ++
>   [CArrayDef vb nodeInfoType (pappInfoTable f)
>              [pappInfo f i n | i <- [0..n-1]]]

> evalDef :: CVisibility -> Name -> Int -> [CTopDecl]
> evalDef vb f n =
>   [evalDecl f | vb == CPublic] ++
>   [CVarDef vb nodeInfoType (nodeInfo f) (funInfo f n)]

> lazyDef :: CVisibility -> Name -> Int -> [CTopDecl]
> lazyDef vb f n =
>   [lazyDecl f | vb == CPublic] ++
>   [CppCondDecls (CExpr "!COPY_SEARCH_SPACE")
>      [CArrayDef vb nodeInfoType (lazyInfoTable f)
>                 (map (CStruct . map CInit) [suspinfo,queuemeinfo,indirinfo])]
>      [CArrayDef vb nodeInfoType (lazyInfoTable f)
>                 [CStruct (map CInit suspinfo)]]]
>   where suspinfo =
>           [CExpr "LAZY_KIND",CExpr "UPD_TAG",suspendNodeSize n,
>            gcPointerTable,CString (undecorate (demangle f)),
>            CExpr (lazyFunc n),noApply,CExpr (cName f),notFinalized]
>         queuemeinfo =
>           [CExpr "LAZY_KIND",CExpr "QUEUEME_TAG",suspendNodeSize n,
>            gcPointerTable,noName,CExpr "eval_queueMe",noApply,noEntry,
>            notFinalized]
>         indirinfo =
>           [CExpr "INDIR_KIND",CInt 0,suspendNodeSize n,
>            gcPointerTable,noName,CExpr "eval_indir",noApply,noEntry,
>            notFinalized]

> fun0Def :: CVisibility -> Name -> Int -> [CTopDecl]
> fun0Def vb f n =
>   [fun0Decl f | vb == CPublic] ++
>   [CVarDef vb (CConstType "struct closure_node") (constFunc f)
>            (CStruct [CInit (info f n),CStruct [CInit CNull]])]
>   where info f n
>           | n == 0 = addr (nodeInfo f)
>           | otherwise = CExpr (pappInfoTable f)

> pappInfo :: Name -> Int -> Int -> CInitializer
> pappInfo f i n = CStruct (map CInit funinfo)
>   where funinfo =
>           [CExpr "PAPP_KIND",CInt (n - i),closureNodeSize i,gcPointerTable,
>            CString (undecorate (demangle f)),CExpr "eval_whnf",
>            CExpr (applyFunc i n),CExpr (cName f),notFinalized]

> funInfo :: Name -> Int -> CInitializer
> funInfo f n = CStruct (map CInit funinfo)
>   where funinfo =
>           [CExpr "LAZY_KIND",CExpr "NOUPD_TAG",closureNodeSize n,
>            gcPointerTable,CString (undecorate (demangle f)),
>            CExpr (evalFunc n),noApply,CExpr (cName f),notFinalized]

\end{verbatim}
\subsection{Code Generation}
The compiler transforms each abstract machine code function into a
list of continuation passing style functions, and translates all of
these functions into distinct C functions. In addition, the compiler
generates the evaluation code for the fully applied closure node and
the suspend node associated with the abstract machine code function.
\begin{verbatim}

> function :: CVisibility -> Name -> [Name] -> Stmt -> [CTopDecl]
> function vb f vs st = funcDefs vb f vs (cpsFunction f vs st)

> applyFunction :: Int -> Int -> CTopDecl
> applyFunction m n = CFuncDef CPrivate (applyFunc m n) (applyCode m n)

> evalFunction :: Int -> CTopDecl
> evalFunction n = CFuncDef CPrivate (evalFunc n) (evalCode n)

> lazyFunction :: Int -> CTopDecl
> lazyFunction n = CFuncDef CPrivate (lazyFunc n) (lazyCode n)

> conFunction :: CVisibility -> Name -> Int -> [CTopDecl]
> conFunction vb f n = function vb f vs (Return (Constr f vs))
>   where vs = [Name ('v' : show i) | i <- [1..n]]

> apFunction :: Name -> Int -> [CTopDecl]
> apFunction f n = funcDefs CPrivate f vs (cpsApply f vs)
>   where vs = [Name ('v' : show i) | i <- [1..n]]

> instFunction :: CVisibility -> Name -> Int -> CTopDecl
> instFunction vb c n =
>   CFuncDef vb (instFunc c)
>            (funCode False (cpsInst (Name "") v (ConstrCase c vs)))
>   where v:vs = [Name ('v' : show i) | i <- [0..n]]

> litInstFunction :: Literal -> CTopDecl
> litInstFunction l =
>   CFuncDef CPrivate (litInstFunc l)
>            (funCode False (cpsInst (Name "") (Name "v0") (LitCase l)))

> funcDefs :: CVisibility -> Name -> [Name] -> [CPSFunction] -> [CTopDecl]
> funcDefs vb f vs (k:ks) =
>   map privFuncDecl ks ++ entryDef vb f vs k : map funcDef ks

> privFuncDecl :: CPSFunction -> CTopDecl
> privFuncDecl k = CFuncDecl CPrivate (cpsName k)

> entryDef :: CVisibility -> Name -> [Name] -> CPSFunction -> CTopDecl
> entryDef vb f vs k
>   | null (cpsEnv k) =
>       CFuncDef vb (cpsName k) (entryCode f (length vs) : funCode True k)
>   | otherwise = error ("internal error: entryDef " ++ demangle f)

> funcDef :: CPSFunction -> CTopDecl
> funcDef k = CFuncDef CPrivate (cpsName k) (funCode False k)

> entryCode :: Name -> Int -> CStmt
> entryCode f n =
>   CProcCall "TRACE_FUN" [CString (undecorate (demangle f)),CInt n]

\end{verbatim}
The compiler generates a C function from every CPS function. At the
beginning of a function, stack and heap checks are performed if
necessary. After the heap check, the function's arguments and local
variables are loaded from the argument registers and the stack. When
generating code for the cases in a \texttt{switch} statement, we try
to reuse these variables. However, if the case code performs a heap
check, the variables have to be reloaded because the garbage collector
does not trace local variables. Note that the code generated by
\texttt{caseCode} is enclosed in a \texttt{CBlock} so that the
declarations generated by \texttt{loadVars} are not moved to a place
where they might inadvertently shadow the variables loaded at the
beginning of the function.
\begin{verbatim}

> funCode :: Bool -> CPSFunction -> [CStmt]
> funCode ent (CPSFunction f _ vs ws st) =
>   elimUnused (stackCheck us st ++ heapCheck us (allocSize consts ds tys) ++
>               loadVars us ++ constDefs consts ds ++ cCode f consts us st [])
>   where us = (ent,vs,ws)
>         ds = concat dss
>         (tys,dss) = allocs st
>         consts = constants dss

> caseCode :: Name -> (Bool,[Name],[Name]) -> Name -> CPSTag -> CPSStmt
>          -> [CStmt]
> caseCode f vs v t st =
>   [CBlock (stackCheck vs st ++ heapCheck' vs (allocSize consts ds tys) ++
>            fetchArgs v t ++ constDefs consts ds ++ cCode f consts vs st [])]
>   where ds = concat dss
>         (tys,dss) = allocs st
>         consts = constants dss
>         heapCheck' vs n = if null sts then [] else sts ++ loadVars vs
>           where sts = heapCheck vs n

\end{verbatim}
The evaluation code for non-updatable lazy application nodes just
loads the arguments from the closure node and then jumps to the
function's entry point. In addition to this, the evaluation code for
an updatable lazy application node also changes the node into a
queue-me node, which prevents the node from being evaluated again, and
pushes an update frame onto the stack, which ensures that the node is
overwritten with (an indirection to) its result after the application
has been evaluated. If an update frame is already on the top of the
stack, the suspended application node is overwritten with an
indirection node pointing to the queue-me node from the update frame
and no additional update frame is pushed onto the stack. This avoids a
potential stack overflow when performing tail calls to a variable
instead of a known function.

The application entry points of partial application nodes use a
special calling convention where the additional arguments and the
return address are expected on the stack rather than in argument
registers and the return address register, respectively. This calling
convention is used because it allows the code to move the additional
arguments only once in the common case where a partial application is
applied to exactly its missing arguments.
\begin{verbatim}

> applyCode :: Int -> Int -> [CStmt]
> applyCode m n =
>   localVar v (Just (reg 0)) :
>   [setReg i (arg i) | i <- [0..m-1]] ++
>   [setReg i (stk (i-m)) | i <- [m..n-1]] ++
>   [setRet (CCast labelType (stk (n-m))),
>    incrSp (n-m+1),
>    gotoExpr (field v "info->entry")]
>   where v = Name "clos"
>         arg = element (field v "c.args")
>         setArg i f j = setReg i (f j)

> evalCode :: Int -> [CStmt]
> evalCode n =
>   localVar v (Just (reg 0)) :
>   [setReg i (arg i) | i <- [0..n-1]] ++
>   [gotoExpr (field v "info->entry")]
>   where v = Name "clos"
>         arg = element (field v "c.args")

> lazyCode :: Int -> [CStmt]
> lazyCode n =
>   CIf (CFunCall "!is_local_space" [CField (reg 0) "s.spc"])
>       [CProcCall "suspend_search" [CInt 1,CField (reg 0) "s.spc"]]
>       [] :
>   loadVars vs0 ++
>   CLocalVar labelType "entry" (Just (field v "info->entry")) :
>   zipWith fetchArg vs [0..] ++
>   CIf (CRel (var retIpName) "==" (CExpr "update"))
>       (localVar v' (Just (stk 0)) : lockIndir v v')
>       (stackCheck vs0 (CPSWithCont k (CPSExec undefined vs)) ++
>        saveCont vs0 [] [] [k] ++
>        [setRet (CExpr "update")] ++
>        lock v) :
>   zipWith setArg [0..] vs ++
>   [goto "entry"]
>   where v = Name "susp"
>         v' = Name "que"
>         vs = [Name ('v' : show i) | i <- [1..n]]
>         vs0 = (True,[v],[])
>         k = CPSCont (CPSFunction (Name (lazyFunc n)) 0 [] [v] undefined)
>         arg = element (field v "s.args")
>         fetchArg v i = localVar v (Just (arg i))
>         setArg i v = setReg i (var v)

\end{verbatim}
The CPS entry function of an abstract machine code function receives
its return address in the return address register, whereas all
continuation functions must load the return address from the stack. In
order to hide this difference from the remaining code, we load the
return address into a local variable when the function's arguments are
loaded.

When saving the arguments and local variables before leaving a
function, we avoid saving variables that were loaded from the same
register or the same offset in the stack because the optimizer of the
Gnu C compiler does not detect such redundant save operations.
Furthermore, \texttt{saveVars} takes care of saving the return address
to the stack and keeping it on the stack as appropriate.
\begin{verbatim}

> loadVars :: (Bool,[Name],[Name]) -> [CStmt]
> loadVars (ent,vs,ws) =
>   zipWith (loadVar reg) vs [0..] ++
>   zipWith (loadVar stk) ws [0..] ++
>   [CLocalVar labelType (show retIpName) (Just (retIp ent))]
>   where loadVar f v i = localVar v (Just (f i))
>         retIp True = regRet
>         retIp False = CCast labelType (stk (length ws))

> fetchArgs :: Name -> CPSTag -> [CStmt]
> fetchArgs _ (CPSLitCase _) = []
> fetchArgs v (CPSConstrCase _ vs) =
>   assertRel (CFunCall "closure_argc" [var v]) "==" (CInt (length vs)) :
>   zipWith fetchArg vs [0..]
>   where arg = element (field v "c.args")
>         fetchArg v i = localVar v (Just (arg i))
> fetchArgs _ CPSFreeCase = []
> fetchArgs _ CPSDefaultCase = []

> saveVars :: (Bool,[Name],[Name]) -> Bool -> [CExpr] -> [CExpr] -> [CStmt]
> saveVars (ent,vs0,ws0) ret vs ws =
>   [incrSp d | d /= 0] ++
>   [setReg i v | (i,v0,v) <- zip3 [0..] vs0' vs, v0 /= v] ++
>   [setStk i w | (i,w0,w) <- zip3 [0..] ws0'' ws', w0 /= w]
>   where d = length ws0' - length ws'
>         ws' = ws ++ [retIpExpr | not ret]
>         vs0' = map var vs0 ++ repeat (CExpr "")
>         ws0' = map var ws0 ++ [retIpExpr | not ent]
>         ws0'' =
>           if d >= 0 then drop d ws0' else replicate (-d) (CExpr "") ++ ws0'
>         retIpExpr = asNode (var retIpName)

> updVar :: (Bool,[Name],[Name]) -> Name -> CStmt
> updVar (_,vs,ws) v =
>   case (elemIndex v vs,elemIndex v ws) of
>     (Just n,_) -> setReg n (var v)
>     (_,Just n) -> setStk n (var v)
>     _ -> error ("updVar " ++ show v)

\end{verbatim}
When computing the heap requirements of a function, we have to take
into account nodes that are allocated explicitly in \texttt{return}
and \texttt{let} statements and implicitly for the results of
\texttt{ccall} statements, but can ignore nodes which are allocated
outside of the heap, i.e., literal constants and character nodes.

Note that we use the same temporary name for the node allocated in
\texttt{CPSReturn} and \texttt{CPSUnify} statements. This is safe
because constants are allocated per block, not per CPS function.
\begin{verbatim}

> heapCheck :: (Bool,[Name],[Name]) -> CExpr -> [CStmt]
> heapCheck (_,vs,_) n =
>   [CProcCall "CHECK_HEAP" [CInt (length vs),n] | n /= CInt 0]

> allocSize :: FM Name CExpr -> [Bind] -> [CArgType] -> CExpr
> allocSize consts ds tys =
>   foldr add (CInt 0)
>         ([ctypeSize ty | ty <- tys] ++
>          [nodeSize n | Bind v n <- ds, not (isConstant consts v)])

> allocs :: CPSStmt -> ([CArgType],[[Bind]])
> allocs (CPSReturn e) = ([],[[Bind resName e]])
> allocs (CPSCCall (Just ty) _) = ([ty],[])
> allocs (CPSUnify _ e) = ([],[[Bind resName e]])
> allocs (CPSDelayNonLocal _ st) = allocs st
> allocs (CPSSeq st1 st2) = allocs0 st1 (allocs st2)
>   where allocs0 (v :<- Return e) ~(tys,dss) = (tys,[Bind v e]:dss)
>         allocs0 (_ :<- CCall _ (Just ty) _) ~(tys,dss) = (ty:tys,dss)
>         allocs0 (v :<- Seq st1 st2) as = allocs0 st1 (allocs0 (v :<- st2) as)
>         allocs0 (Let ds) ~(tys,dss) = (tys,ds:dss)
>         allocs0 _ as = as
> allocs (CPSWithCont _ st) = allocs st
> allocs _ = ([],[])

> nodeSize :: Expr -> CExpr
> nodeSize (Lit _) = CInt 0
> nodeSize (Constr _ vs) = closureNodeSize (length vs)
> nodeSize (Papp _ vs) = closureNodeSize (length vs)
> nodeSize (Closure _ vs) = closureNodeSize (length vs)
> nodeSize (Lazy f vs) = suspendNodeSize (length vs)
> nodeSize Free = CExpr "variable_node_size"
> nodeSize (Var _) = CInt 0

> ctypeSize :: CArgType -> CExpr
> ctypeSize TypeBool = CInt 0
> ctypeSize TypeChar = CExpr "char_node_size"
> ctypeSize TypeInt = CExpr "int_node_size"
> ctypeSize TypeFloat = CExpr "float_node_size"
> ctypeSize TypePtr = CExpr "ptr_node_size"
> ctypeSize TypeFunPtr = CExpr "ptr_node_size"
> ctypeSize TypeStablePtr = CExpr "ptr_node_size"
> ctypeSize TypeNodePtr = CInt 0

> closureNodeSize, suspendNodeSize :: Int -> CExpr
> closureNodeSize n = CFunCall "closure_node_size" [CInt n]
> suspendNodeSize n = CFunCall "suspend_node_size" [CInt n]

\end{verbatim}
The maximum stack depth of a function is simply the difference between
the number of variables saved on the stack when the function is
entered and the number of variables pushed onto the stack when calling
the continuation. Note that the stack check must take the return
address into account, which is saved on the stack except in the CPS
entry function of an abstract machine code function. In case of a
\texttt{CPSSwitch} statement, every alternative is responsible for
performing a stack check.
\begin{verbatim}

> stackCheck :: (Bool,[Name],[Name]) -> CPSStmt -> [CStmt]
> stackCheck (ent,_,ws) st = [CProcCall "CHECK_STACK" [CInt depth] | depth > 0]
>   where depth = stackDepth st - length (ws ++ [retIpName | not ent])

> stackDepth :: CPSStmt -> Int
> stackDepth (CPSJump k) = stackDepthCont k
> stackDepth (CPSReturn _) = 0
> stackDepth (CPSEnter _) = 0
> stackDepth (CPSExec _ _) = 0
> stackDepth (CPSCCall _ _) = 0
> stackDepth (CPSApply _ vs) = 2 + length vs
> stackDepth (CPSUnify _ _) = 0
> stackDepth (CPSDelay _) = 0
> stackDepth (CPSDelayNonLocal _ st) = stackDepth st
> stackDepth (CPSSeq _ st) = stackDepth st
> stackDepth (CPSWithCont k st) = stackDepthCont k + stackDepth st
> stackDepth (CPSSwitch _ _ _) = 0
> stackDepth (CPSChoices _ (k:_)) = 1 + stackDepthCont k

> stackDepthCont :: CPSCont -> Int
> stackDepthCont k = 1 + length (contVars k)

\end{verbatim}
All constants that are used in a function are preallocated in a static
array \texttt{Node *constants[]} at the beginning of that function.
The following functions compute the set of variables which are bound
to constants together with their respective initializer expressions.
Recall that literals as well as nullary data constructors and partial
applications without arguments are allocated globally in order to
improve sharing.

In order to detect constants in recursive data definitions
effectively, the declarations in \texttt{let} statements should be
split into minimal binding groups.
\begin{verbatim}

> isConstant :: FM Name CExpr -> Name -> Bool
> isConstant consts v = isJust (lookupFM v consts)

> constants :: [[Bind]] -> FM Name CExpr
> constants dss = fromListFM $ snd $
>   mapAccumL init 0 [(v,n) | ds <- dss, Bind v n <- ds, v `elemSet` vs0]
>   where vs0 = constVars dss
>         init o (v,Lit c) = (o,(v,literal c))
>         init o (v,Constr c vs)
>           | null vs = (o,(v,constRef (constNode c)))
>           | otherwise = (o + length vs + 1,(v,constant o))
>         init o (v,Papp f vs)
>           | null vs = (o,(v,constRef (constFunc f)))
>           | otherwise = (o + length vs + 1,(v,constant o))
>         init o (v,Closure f vs)
>           | null vs = (o,(v,constRef (constFunc f)))
>           | otherwise = (o + length vs + 1,(v,constant o))
>         init o (v,Var v') = (o,(v,var v'))
>         init _ (v,n) = error ("internal error: constants.init" ++ show n)
>         constant = asNode . add (CExpr constArray) . CInt

> constVars :: [[Bind]] -> Set Name
> constVars = foldl_strict addConst zeroSet
>   where addConst vs0 ds = if all (isConst vs0') ns then vs0' else vs0
>           where vs0' = foldr addToSet vs0 vs
>                 (vs,ns) = unzip [(v,n) | Bind v n <- ds]
>         isConst _ (Lit _) = True
>         isConst vs0 (Constr _ vs) = all (`elemSet` vs0) vs
>         isConst vs0 (Papp _ vs) = all (`elemSet` vs0) vs
>         isConst vs0 (Closure _ vs) = all (`elemSet` vs0) vs
>         isConst _ (Lazy _ _) = False
>         isConst _ Free = False
>         isConst vs0 (Var v) = v `elemSet` vs0

> literal :: Literal -> CExpr
> literal (Char c)
>   | ord c < 0x100 = asNode (CAdd (CExpr "char_table") (CInt (ord c)))
>   | otherwise = constRef (constChar c)
> literal (Int i) = CExpr (constInt i)
> literal (Float f) = constRef (constFloat f)

> constDefs :: FM Name CExpr -> [Bind] -> [CStmt]
> constDefs consts ds =
>   [CStaticArray nodeConstPtrType constArray is | not (null is)]
>   where is = constData consts ds

> constData :: FM Name CExpr -> [Bind] -> [CInitializer]
> constData consts ds = map (CInit . asNode) $ foldr constInit [] ds
>   where constInit (Bind v (Constr c vs)) is
>           | not (null vs) && isConstant consts v =
>               addr (nodeInfo c) : map arg vs ++ is
>         constInit (Bind v (Papp f vs)) is
>           | not (null vs) && isConstant consts v =
>               CExpr (pappInfoTable f) `add` CInt (length vs) :
>               map arg vs ++ is
>         constInit (Bind v (Closure f vs)) is
>           | not (null vs) && isConstant consts v =
>               addr (nodeInfo f) : map arg vs ++ is
>         constInit _ is = is
>         arg v = fromJust (lookupFM v consts)

> freshNode :: FM Name CExpr -> Name -> Expr -> [CStmt]
> freshNode consts v n = allocNode consts d ++ initNode consts d
>   where d = Bind v n

> allocNode :: FM Name CExpr -> Bind -> [CStmt]
> allocNode consts (Bind v n) =
>   case lookupFM v consts of
>     Just e -> [localVar v (Just e)]
>     Nothing ->
>       case n of
>         Lit c -> [localVar v (Just (literal c))]
>         Var v' -> [localVar v (Just (var v'))]
>         _ -> [localVar v (Just alloc),incrAlloc (nodeSize n)]

> initNode :: FM Name CExpr -> Bind -> [CStmt]
> initNode _ (Bind v (Lit _)) = []
> initNode consts (Bind v (Constr c vs))
>   | isConstant consts v = []
>   | otherwise = initConstr v c vs
> initNode consts (Bind v (Papp f vs))
>   | isConstant consts v = []
>   | otherwise = initPapp v f vs
> initNode consts (Bind v (Closure f vs))
>   | isConstant consts v = []
>   | otherwise = initClosure v f vs
> initNode _ (Bind v (Lazy f vs)) = initLazy v f vs
> initNode _ (Bind v Free) = initFree v
> initNode _ (Bind v (Var _)) = []

> initConstr :: Name -> Name -> [Name] -> [CStmt]
> initConstr v c vs =
>   setField v "info" (addr (nodeInfo c)) : initArgs v "c.args" vs

> initPapp :: Name -> Name -> [Name] -> [CStmt]
> initPapp v f vs =
>   setField v "info" (CExpr (pappInfoTable f) `add` CInt (length vs)) :
>   initArgs v "c.args" vs

> initClosure :: Name -> Name -> [Name] -> [CStmt]
> initClosure v f vs =
>   setField v "info" (addr (nodeInfo f)) : initArgs v "c.args" vs

> initLazy :: Name -> Name -> [Name] -> [CStmt]
> initLazy v f vs =
>   setField v "info" (CExpr (lazyInfoTable f)) :
>   setField v "s.spc" (CExpr "regs.ss") :
>   if null vs then
>     [setElem (lfield v "s.args") 0 CNull]
>   else
>     initArgs v "s.args" vs

> initFree :: Name -> [CStmt]
> initFree v =
>   [setField v "info" (CExpr "variable_info_table"),
>    setField v "v.spc" (CExpr "regs.ss"),
>    setField v "v.wq" CNull,
>    setField v "v.cstrs" CNull]

> initArgs :: Name -> String -> [Name] -> [CStmt]
> initArgs v f vs = zipWith (initArg (lfield v f)) [0..] vs
>   where initArg v1 i v2 = setElem v1 i (var v2)

\end{verbatim}
Every abstract machine code statement is translated by its own
translation function.
\begin{verbatim}

> cCode :: Name -> FM Name CExpr -> (Bool,[Name],[Name]) -> CPSStmt -> [CPSCont]
>       -> [CStmt]
> cCode _ _ vs0 (CPSJump k) ks = jump vs0 k ks
> cCode _ consts vs0 (CPSReturn e) ks =
>   case e of
>     Var v -> ret vs0 v ks
>     _ -> freshNode consts resName e ++ ret vs0 resName ks
> cCode _ _ vs0 (CPSEnter v) ks = enter vs0 v ks
> cCode _ _ vs0 (CPSExec f vs) ks = exec vs0 f vs ks
> cCode _ _ vs0 (CPSCCall ty cc) ks = cCall ty resName cc ++ ret vs0 resName ks
> cCode _ _ vs0 (CPSApply v vs) ks = apply vs0 v vs ks
> cCode _ consts vs0 (CPSUnify v e) ks =
>   case e of
>     Var v' -> unifyVar vs0 v v' ks
>     _ -> freshNode consts resName e ++ unifyVar vs0 v resName ks
> cCode _ _ vs0 (CPSDelay v) ks = delay vs0 v ks
> cCode f consts vs0 (CPSDelayNonLocal v st) ks =
>   delayNonLocal vs0 v ks ++ cCode f consts vs0 st ks
> cCode f consts vs0 (CPSSeq st1 st2) ks =
>   cCode0 consts st1 ++ cCode f consts vs0 st2 ks
> cCode f consts vs0 (CPSWithCont k st) ks = cCode f consts vs0 st (k:ks)
> cCode f _ vs0 (CPSSwitch tagged v cases) [] =
>   switchOnTerm f tagged vs0 v
>                [(t,caseCode f vs0 v t st) | CaseBlock t st <- cases]
> cCode _ _ vs0 (CPSChoices v ks) ks' = choices vs0 v ks ks'

> cCode0 :: FM Name CExpr -> Stmt0 -> [CStmt]
> cCode0 _ (Lock v) = lock v
> cCode0 _ (Update v1 v2) = update v1 v2
> cCode0 consts (v :<- Return e) = freshNode consts v e
> cCode0 consts (v :<- CCall _ ty cc) = cCall ty v cc
> cCode0 consts (v :<- Seq st1 st2) =
>   cCode0 consts st1 ++ cCode0 consts (v :<- st2)
> cCode0 consts (Let ds) =
>   concatMap (allocNode consts) ds ++ concatMap (initNode consts) ds

> jump :: (Bool,[Name],[Name]) -> CPSCont -> [CPSCont] -> [CStmt]
> jump vs0 k ks = saveCont vs0 [] [] (k:ks) ++ [gotoRet (k:ks)]

> ret :: (Bool,[Name],[Name]) -> Name -> [CPSCont] -> [CStmt]
> ret vs0 v ks = saveCont vs0 [v] [] ks ++ [gotoRet ks]

> enter :: (Bool,[Name],[Name]) -> Name -> [CPSCont] -> [CStmt]
> enter vs0 v ks =
>   saveCont vs0 [v] [] ks ++
>   [kindSwitch v [updVar (null ks,[v],[]) v] (Just [])
>               [CCase "LAZY_KIND"
>                      (saveRet vs0 ks ++ [gotoExpr (field v "info->eval")])],
>    gotoRet ks]

> exec :: (Bool,[Name],[Name]) -> Name -> [Name] -> [CPSCont] -> [CStmt]
> exec vs0 f vs ks = saveCont vs0 vs [] ks ++ saveRet vs0 ks ++ [goto (cName f)]

> saveCont :: (Bool,[Name],[Name]) -> [Name] -> [Name] -> [CPSCont] -> [CStmt]
> saveCont vs0 vs ws ks =
>   saveVars vs0 (null ks) (map var vs) (map var ws ++ drop 1 ws')
>   where ws' = concatMap contFrame ks
>         contFrame k = asNode (CExpr (contName k)) : map var (contVars k)

> saveRet :: (Bool,[Name],[Name]) -> [CPSCont] -> [CStmt]
> saveRet (ent,_,_) [] = [setRet (var retIpName) | not ent]
> saveRet _ (k:_) = [setRet (CExpr (contName k))]

> gotoRet :: [CPSCont] -> CStmt
> gotoRet ks = goto (contIp ks)
>   where contIp [] = show retIpName
>         contIp (k:_) = contName k

> lock :: Name -> [CStmt]
> lock v =
>   [assertLazyNode v "UPD_TAG",
>    CppCondStmts "!COPY_SEARCH_SPACE"
>      [CIf (CRel (CCast wordPtrType (var v)) "<" (CExpr "regs.hlim"))
>           [CProcCall "DO_SAVE" [var v,CExpr "q.wq"],
>            CIncrBy (lfield v "info") (CInt 1)]
>           [setField v "info" (CExpr "queueMe_info_table")]]
>      [setField v "info" (CExpr "queueMe_info_table")],
>    setField v "q.wq" CNull]

> update :: Name -> Name -> [CStmt]
> update v1 v2 =
>   [assertLazyNode v1 "QUEUEME_TAG",
>    CLocalVar (CType "ThreadQueue") wq (Just (field v1 "q.wq")),
>    CppCondStmts "!COPY_SEARCH_SPACE"
>      [CProcCall "SAVE" [var v1,CExpr "q.wq"],
>       CIncrBy (lfield v1 "info") (CInt 1)]
>      [setField v1 "info" (addr "indir_info")],
>    setField v1 "n.node" (var v2),
>    CIf (CExpr wq) [procCall "wake_threads" [wq]] []]
>   where wq = "wq"

> lockIndir :: Name -> Name -> [CStmt]
> lockIndir v1 v2 =
>   [assertLazyNode v2 "QUEUEME_TAG",
>    CppCondStmts "!COPY_SEARCH_SPACE"
>      [CIf (CRel (CCast wordPtrType (var v1)) "<" (CExpr "regs.hlim"))
>           [CProcCall "DO_SAVE" [var v1,CExpr "n.node"],
>            CIncrBy (lfield v1 "info") (CInt 2)]
>           [setField v1 "info" (addr "indir_info")]]
>      [setField v1 "info" (addr "indir_info")],
>    setField v1 "n.node" (var v2)]

> assertLazyNode :: Name -> String -> CStmt
> assertLazyNode v tag =
>   rtsAssertList [isTaggedPtr v,CRel (nodeKind v) "==" (CExpr "LAZY_KIND"),
>                  CRel (nodeTag v) "==" (CExpr tag),
>                  CFunCall "is_local_space" [field v "s.spc"]]

> unifyVar :: (Bool,[Name],[Name]) -> Name -> Name -> [CPSCont] -> [CStmt]
> unifyVar vs0 v n ks =
>   saveCont vs0 [v,n] [] ks ++ saveRet vs0 ks ++ [goto "bind_var"]

> delay :: (Bool,[Name],[Name]) -> Name -> [CPSCont] -> [CStmt]
> delay vs0 v ks = saveCont vs0 [v] [] ks ++ saveRet vs0 ks ++ [goto "sync_var"]

> delayNonLocal :: (Bool,[Name],[Name]) -> Name -> [CPSCont] -> [CStmt]
> delayNonLocal vs0 v ks =
>   [CIf (CFunCall "!is_local_space" [field v "v.spc"])
>        (delay vs0 v ks)
>        []]

> choices :: (Bool,[Name],[Name]) -> Maybe Name -> [CPSCont] -> [CPSCont]
>         -> [CStmt]
> choices vs0 v ks ks' =
>   CStaticArray constLabelType choices
>                (map (CInit . CExpr . contName) ks ++ [CInit CNull]) :
>   localVar ips (Just (asNode (CExpr choices))) :
>   saveCont vs0 [] [ips] (head ks : ks') ++
>   [CppCondStmts "YIELD_NONDET"
>      [CIf (CExpr "regs.rq") (yieldCall v) []]
>      [],
>    goto "regs.handlers->choices"]
>   where ips = Name "_choice_ips"
>         choices = "_choices"
>         yieldCall (Just v) =
>           saveVars vs0 (fst3 vs0) [var v] (map var (thd3 vs0)) ++
>           [setRet (CExpr "flex_yield_resume"),
>            goto "yield_delay_thread"]
>         yieldCall Nothing =
>           [setRet (CExpr "regs.handlers->choices"),
>            goto "yield_thread"]

> failAndBacktrack :: Name -> [CStmt]
> failAndBacktrack f =
>   [setReg 0 (asNode (CString (undecorate (demangle f) ++ ": no match"))),
>    goto "regs.handlers->fail"]

\end{verbatim}
Code generation for \texttt{CPSSwitch} statements is a little bit more
complicated because matching literal constants requires two nested
switches. The outer switch matches the common tag and the inner switch
the literal's value. Furthermore, integer literals are either encoded
in the pointer or stored in a heap allocated node depending on their
value and the setting of the preprocessor constant
\texttt{NO\_POINTER\_TAGS}, which forces heap allocation of all
integer numbers when set to a non-zero value.
\begin{verbatim}

> switchOnTerm :: Name -> Bool -> (Bool,[Name],[Name]) -> Name
>              -> [(CPSTag,[CStmt])] -> [CStmt]
> switchOnTerm f tagged vs0 v cases =
>   kindSwitch v [updVar vs0 v] tagCase otherCases :
>   head (dflts ++ [failAndBacktrack f])
>   where (lits,constrs,vars,dflts) = foldr partition ([],[],[],[]) cases
>         (chars,ints,floats) = foldr litPartition ([],[],[]) lits
>         tagCase
>           | tagged =
>               Just [CppCondStmts "NO_POINTER_TAGS"
>                       [CProcCall "curry_panic"
>                                  [CString "impossible: is_tagged_int(%p)\n",
>                                   var v]]
>                       [intSwitch (CFunCall "untag_int" [var v]) ints]
>                    | not (null ints)]
>           | otherwise = Nothing
>         otherCases =
>           map varCase vars ++ [charCase | not (null chars)] ++
>           [intCase | not (null ints)] ++ [floatCase | not (null floats)] ++
>           [constrCase | not (null constrs)]
>         varCase = CCase "LVAR_KIND"
>         charCase = CCase "CHAR_KIND" [charSwitch v chars,CBreak]
>         intCase = CCase "INT_KIND" [intSwitch (field v "i.i") ints,CBreak]
>         floatCase = CCase "FLOAT_KIND" (floatSwitch v floats ++ [CBreak])
>         constrCase = CCase "CAPP_KIND" [tagSwitch v constrs,CBreak]
>         partition (t,stmts) ~(lits,constrs,vars,dflts) =
>           case t of
>              CPSLitCase l -> ((l,stmts) : lits,constrs,vars,dflts)
>              CPSConstrCase c _ -> (lits,(c,stmts) : constrs,vars,dflts)
>              CPSFreeCase -> (lits,constrs,stmts : vars,dflts)
>              CPSDefaultCase -> (lits,constrs,vars,stmts : dflts)
>         litPartition (Char c,stmts) ~(chars,ints,floats) =
>           ((c,stmts):chars,ints,floats)
>         litPartition (Int i,stmts) ~(chars,ints,floats) =
>           (chars,(i,stmts):ints,floats)
>         litPartition (Float f,stmts) ~(chars,ints,floats) =
>           (chars,ints,(f,stmts):floats)

> kindSwitch :: Name -> [CStmt] -> Maybe [CStmt] -> [CCase] -> CStmt
> kindSwitch v upd tagCase cases =
>   CLoop [taggedSwitch tagCase (CSwitch (nodeKind v) allCases),CBreak]
>   where allCases =
>           CCase "INDIR_KIND"
>             (setVar v (field v "n.node") : upd ++ [CContinue]) :
>           cases
>         taggedSwitch (Just sts) switch
>           | null sts = CIf (isTaggedPtr v) [switch] []
>           | otherwise = CIf (isTaggedInt v) sts [switch]
>         taggedSwitch Nothing switch = switch

> charSwitch :: Name -> [(Char,[CStmt])] -> CStmt
> charSwitch v cases =
>   CSwitch (field v "ch.ch") [CCase (show (ord c)) stmts | (c,stmts) <- cases]

> intSwitch :: CExpr -> [(Int,[CStmt])] -> CStmt
> intSwitch e cases = CSwitch e [CCase (show i) stmts | (i,stmts) <- cases]

> floatSwitch :: Name -> [(Double,[CStmt])] -> [CStmt]
> floatSwitch v cases =
>   getFloat "d" (var v) ++ foldr (match (CExpr "d")) [] cases
>   where match v (f,stmts) rest = [CIf (CRel v "==" (CFloat f)) stmts rest]

> tagSwitch :: Name -> [(Name,[CStmt])] -> CStmt
> tagSwitch v cases =
>   CSwitch (nodeTag v) [CCase (dataTag c) stmts | (c,stmts) <- cases]

\end{verbatim}
The code for \texttt{CPSApply} statements has to check to how many
arguments a partial application is applied. If there are too few
arguments, a new partial application node is returned, which includes
the additional arguments. Otherwise, the application is entered through
its application entry point. If the closure is applied to too many
arguments, the code generated by \texttt{apply} creates a return frame
on the stack, which takes care of applying the result of the
application to the surplus arguments. Note that the apply entry point
of a partial application node is called with the additional arguments
and return address on the stack. Only the partial application node
itself is passed in a register.
\begin{verbatim}

> apply :: (Bool,[Name],[Name]) -> Name -> [Name] -> [CPSCont] -> [CStmt]
> apply vs0 v vs ks =
>   CSwitch (nodeTag v)
>           [CCase (show i)
>                  (applyExec vs0 v (splitAt i vs) ks) | i <- [1..length vs]] :
>   applyPartial vs0 v vs ks

> applyExec :: (Bool,[Name],[Name]) -> Name -> ([Name],[Name]) -> [CPSCont]
>           -> [CStmt]
> applyExec vs0 v (vs,vs') ks =
>   saveCont vs0 [v] [] (apEntry : if null vs' then ks else apCont : ks) ++
>   [gotoExpr (field v "info->apply")]
>   where apEntry = cont undefined 0 [v] vs
>         apCont = cont (apName (length vs' + 1)) 1 [v] vs'
>         cont f n vs ws = CPSCont (CPSFunction f n vs ws undefined)

> applyPartial :: (Bool,[Name],[Name]) -> Name -> [Name] -> [CPSCont]
>              -> [CStmt]
> applyPartial vs0 v vs ks =
>   [assertRel (nodeTag v) ">" (CInt 0),
>    CLocalVar uintType "argc" (Just (CFunCall "closure_argc" [var v])),
>    CLocalVar uintType "sz" (Just (CFunCall "node_size" [var v]))] ++
>   heapCheck vs0 size ++
>   [CBlock (loadVars vs0 ++
>            localVar resName (Just alloc) :
>            incrAlloc size :
>            wordCopy (var resName) (var v) "sz" :
>            CIncrBy (lfield resName "info") (CInt n) :
>            zipWith (setArg (lfield resName "c.args")) [0..] vs ++
>            ret vs0 resName ks)]
>   where n = length vs
>         size = CExpr "sz" `CAdd` CInt n
>         setArg base i v =
>           CAssign (LElem base (CExpr "argc" `add` CInt i)) (var v)

\end{verbatim}
For a foreign function call, the generated code first unboxes all
arguments, then calls the function, and finally boxes the result of
the call. When taking the address of a foreign variable, the code
first loads this address into a temporary variable and then boxes it.
\begin{verbatim}

> cCall :: CRetType -> Name -> CCall -> [CStmt]
> cCall ty v cc = cEval ty v' cc ++ box ty v (CExpr v')
>   where v' = cRetVar v

> cEval :: CRetType -> String -> CCall -> [CStmt]
> cEval ty v (StaticCall f xs) = cFunCall ty v f xs
> cEval ty v1 (DynamicCall v2 xs) =
>   unboxFunPtr ty (map fst xs) f (var v2) : cFunCall ty v1 f xs
>   where f = cArgVar v2
> cEval ty v (StaticAddr x) = cAddr ty v x

> cFunCall :: CRetType -> String -> String -> [(CArgType,Name)] -> [CStmt]
> cFunCall ty v f xs =
>   concat [unbox ty v2 (var v1) | ((ty,v1),v2) <- zip xs vs] ++
>   [callCFun ty v f vs]
>   where vs = map (cArgVar . snd) xs

> cAddr :: CRetType -> String -> String -> [CStmt]
> cAddr Nothing v x = []
> cAddr (Just ty) v x =
>   [CLocalVar (ctype ty) v (Just (CCast (ctype ty) (addr x)))]

> unbox :: CArgType -> String -> CExpr -> [CStmt]
> unbox TypeBool v e =
>   [CLocalVar (ctype TypeBool) v (Just (CField e "info->tag"))]
> unbox TypeChar v e =
>   [CLocalVar (ctype TypeChar) v (Just (CField e "ch.ch"))]
> unbox TypeInt v e =
>   [CLocalVar (ctype TypeInt) v (Just (CFunCall "long_val" [e]))]
> unbox TypeFloat v e = getFloat v e
> unbox TypePtr v e =
>   [CLocalVar (ctype TypePtr) v (Just (CField e "p.ptr"))]
> unbox TypeFunPtr v e =
>   [CLocalVar (ctype TypeFunPtr) v (Just (CField e "p.ptr"))]
> unbox TypeStablePtr v e =
>   [CLocalVar (ctype TypeStablePtr) v (Just (CField e "p.ptr"))]
> unbox TypeNodePtr v e = [CLocalVar (ctype TypeNodePtr) v (Just e)]

> unboxFunPtr :: CRetType -> [CArgType] -> String -> CExpr -> CStmt
> unboxFunPtr ty0 tys v e = CLocalVar ty v (Just (CCast ty (CField e "p.ptr")))
>   where ty = CPointerType
>            $ CFunctionType (maybe voidType ctype ty0) (map ctype tys)

> callCFun :: CRetType -> String -> String -> [String] -> CStmt
> callCFun Nothing _ f vs = procCall f vs
> callCFun (Just ty) v f vs = CLocalVar (ctype ty) v (Just (funCall f vs))

> box :: CRetType -> Name -> CExpr -> [CStmt]
> box Nothing v _ =
>   [localVar v (Just (constRef (constNode (mangle "()"))))]
> box (Just TypeBool) v e =
>   [localVar v (Just (CCond e (const prelTrue) (const prelFalse)))]
>   where const = constRef . constNode
> box (Just TypeChar) v e =
>   [localVar v Nothing,
>    CIf (CRel (CRel e ">=" (CInt 0)) "&&" (CRel e "<" (CInt 0x100)))
>      [setVar v (asNode (CExpr "char_table" `CAdd` e))]
>      [setVar v alloc,
>       setField v "info" (addr "char_info"),
>       setField v "ch.ch" e,
>       incrAlloc (ctypeSize TypeChar)]]
> box (Just TypeInt) v e =
>   [localVar v Nothing,
>    CIf (CFunCall "is_large_int" [e])
>      [setVar v alloc,
>       setField v "info" (addr "int_info"),
>       setField v "i.i" e,
>       incrAlloc (ctypeSize TypeInt)]
>      [CppCondStmts "NO_POINTER_TAGS"
>         [CProcCall "curry_panic"
>                    [CString "impossible: !is_large_int(%ld)\n",e]]
>         [setVar v (CFunCall "tag_int" [e])]]]
> box (Just TypeFloat) v e =
>   [localVar v (Just alloc),
>    setField v "info" (addr  "float_info"),
>    CProcCall "put_double_val" [var v,e],
>    incrAlloc (ctypeSize TypeFloat)]
> box (Just TypePtr) v e =
>   [localVar v Nothing,
>    CIf (CRel e "==" CNull)
>      [setVar v (constRef "null_ptr")]
>      [setVar v alloc,
>       setField v "info" (addr "ptr_info"),
>       setField v "p.ptr" e,
>       incrAlloc (ctypeSize TypePtr)]]
> box (Just TypeFunPtr) v e =
>   [localVar v Nothing,
>    CIf (CRel e "==" CNull)
>      [setVar v (constRef "null_funptr")]
>      [setVar v alloc,
>       setField v "info" (addr "funptr_info"),
>       setField v "p.ptr" e,
>       incrAlloc (ctypeSize TypeFunPtr)]]
> box (Just TypeStablePtr) v e =
>   [localVar v Nothing,
>    CIf (CRel e "==" CNull)
>      [setVar v (constRef "null_stabptr")]
>      [setVar v alloc,
>       setField v "info" (addr "stabptr_info"),
>       setField v "p.ptr" e,
>       incrAlloc (ctypeSize TypeStablePtr)]]
> box (Just TypeNodePtr) v e = [localVar v (Just e)]

> ctype :: CArgType -> CType
> ctype TypeBool = intType
> ctype TypeChar = intType
> ctype TypeInt = longType
> ctype TypeFloat = doubleType
> ctype TypePtr = voidPtrType
> ctype TypeFunPtr = voidPtrType
> ctype TypeStablePtr = voidPtrType
> ctype TypeNodePtr = nodePtrType

\end{verbatim}
As a convenience to the user, we strip the decoration of auxiliary
function names introduced by the debugging transformation when the
name of a function is printed. In particular, the debugger adds the
prefix \texttt{\_debug\#} and a suffix \texttt{\#}$n$ to the name of
the transformed function. Note that the prefix is added to the
unqualified name.
\begin{verbatim}

> undecorate :: String -> String
> undecorate cs =
>   case break ('_' ==) cs of
>     (cs', "") -> dropSuffix cs'
>     (cs', ('_':cs''))
>       | "debug#" `isPrefixOf` cs'' -> cs' ++ undecorate (drop 6 cs'')
>       | otherwise -> cs' ++ '_' : undecorate cs''
>   where dropSuffix cs =
>           case break ('#' ==) cs of
>             (cs',"") -> cs'
>             (cs','#':cs'')
>               | all isDigit cs'' -> cs'
>               | otherwise -> cs' ++ '#' : dropSuffix cs''

\end{verbatim}
The function \texttt{isPublic} is a workaround for distinguishing
private and exported functions without an explicit export list, which
is not yet part of the abstract machine code syntax. This function
uses the following heuristics. All entities whose (demangled) name
ends with a suffix \texttt{.}$n$, where $n$ is a non-empty sequence of
decimal digits are considered private, since that suffix can occur
only for renamed identifiers, and all entities whose (demangled) name
contains one of the substrings \verb"_#lambda" an \verb"_#app" are
considered private, too. These names are used by the compiler for
naming lambda abstractions and the implicit functions introduced for
lifted argument expressions.
\begin{verbatim}

> isPublic, isPrivate :: Name -> Bool
> isPublic x = not (isPrivate x)
> isPrivate (Name x) =
>   any (\cs -> any (`isPrefixOf` cs) [app,lambda]) (tails x) ||
>   case span isDigit (reverse x) of
>     ([],_) -> False
>     (_:_,cs) -> reverse dot `isPrefixOf` cs
>   where Name dot = mangle "."
>         Name app = mangle "_#app"
>         Name lambda = mangle "_#lambda"

\end{verbatim}
In order to avoid some trivial name conflicts with the standard C
library, the names of all Curry functions are prefixed with two
underscores. The integer key of each CPS function is added to the
name, except for the function's main entry point, whose key is
\texttt{0}.

The names of the info vector for a data constructor application and
the info table for a function are constructed by appending the
suffixes \texttt{\_info} and \texttt{\_info\_table}, respectively, to
the name. The suffixes \texttt{\_const} and \texttt{\_function} are
used for constant constructors and functions, respectively.
\begin{verbatim}

> cName :: Name -> String
> cName x = "__" ++ show x

> cPrivName :: Name -> Int -> String
> cPrivName f n
>   | n == 0 = cName f
>   | otherwise = cName f ++ '_' : show n

> cpsName :: CPSFunction -> String
> cpsName (CPSFunction f n _ _ _) = cPrivName f n

> contName :: CPSCont -> String
> contName (CPSCont f) = cpsName f
> contName (CPSInst _ (LitCase l)) = litInstFunc l
> contName (CPSInst _ (ConstrCase c _)) = instFunc c

> constArray :: String
> constArray = "constants"

> applyFunc :: Int -> Int -> String
> applyFunc m n = "apply_clos_" ++ show m ++ "_" ++ show n

> evalFunc, lazyFunc :: Int -> String
> evalFunc n = "eval_clos_" ++ show n
> lazyFunc n = "eval_lazy_" ++ show n

> instFunc :: Name -> String
> instFunc c = cName c ++ "_unify"

> litInstFunc :: Literal -> String
> litInstFunc (Char c) = constChar c ++ "_unify"
> litInstFunc (Int i) = constInt i ++ "_unify"
> litInstFunc (Float f) = constFloat f ++ "_unify"

> nodeInfo, pappInfoTable, lazyInfoTable :: Name -> String
> nodeInfo c = cName c ++ "_info"
> pappInfoTable f = cName f ++ "_papp_info_table"
> lazyInfoTable f = cName f ++ "_lazy_info_table"

> dataTag :: Name -> String
> dataTag c = cName c ++ "_tag"

> closVar :: Name -> String
> closVar v = show v ++ "_clos"

> cArgVar :: Name -> String
> cArgVar v = "_carg" ++ "_" ++ show v

> cRetVar :: Name -> String
> cRetVar v = "_cret" ++ "_" ++ show v

> retIpName :: Name
> retIpName = Name "_ret_ip"

> resName :: Name
> resName = Name "_"

\end{verbatim}
The function \texttt{tupleArity} computes the arity of a tuple
constructor by counting the commas in the -- demangled -- name. Note
that \texttt{()} is \emph{not} a tuple name.
\begin{verbatim}

> isTuple :: Name -> Bool
> isTuple c = isTupleName (demangle c)
>   where isTupleName ('(':',':cs) = dropWhile (',' ==) cs == ")"
>         isTupleName _ = False

> tupleArity :: Name -> Int
> tupleArity c = arity (demangle c)
>   where arity ('(':',':cs)
>           | cs'' == ")" = length cs' + 2
>           where (cs',cs'') = span (',' ==) cs
>         arity _ = error "internal error: tupleArity"

\end{verbatim}
The function \texttt{apArity} returns the arity of an application
function \texttt{@}$_n$. Note that \texttt{@}$_n$ has arity $n+1$
since $n$ denotes the arity of its first argument. The function
\texttt{apName} is the inverse of \texttt{apArity}, i.e., the
following two equations hold
\begin{eqnarray*}
  i & = & \texttt{apArity}(\texttt{apName}(i)) \\
  x & = & \texttt{apName}(\texttt{apArity}(x))
\end{eqnarray*}
provided that $x$ is the name of an application function. Note the
special case for \texttt{@}, which is used instead of \texttt{@}$_1$.
\begin{verbatim}

> isAp :: Name -> Bool
> isAp f = isApName (demangle f)
>   where isApName ('@':cs) = all isDigit cs
>         isApName _ = False

> apArity :: Name -> Int
> apArity f = arity (demangle f)
>   where arity ('@':cs)
>           | null cs = 2
>           | all isDigit cs = read cs + 1
>         arity _ = error "internal error: applyArity"

> apName :: Int -> Name
> apName n = mangle ('@' : if n == 2 then "" else show (n - 1))

> constChar :: Char -> String
> constChar c = "char_" ++ show (ord c)

> constInt :: Int -> String
> constInt i = "int_" ++ mangle (show i)
>   where mangle ('-':cs) = 'M':cs
>         mangle cs = cs

> constFloat :: Double -> String
> constFloat f = "float_" ++ map mangle (show f)
>   where mangle '+' = 'P'
>         mangle '-' = 'M'
>         mangle '.' = '_'
>         mangle c = c

> constNode, constFunc :: Name -> String
> constNode c = cName c ++ "_node"
> constFunc f = cName f ++ "_function"

\end{verbatim}
Here are some convenience functions, which simplify the construction
of the abstract syntax tree.
\begin{verbatim}

> var :: Name -> CExpr
> var v = CExpr (show v)

> localVar :: Name -> Maybe CExpr -> CStmt
> localVar v = CLocalVar nodePtrType (show v)

> setVar :: Name -> CExpr -> CStmt
> setVar v = CAssign (LVar (show v))

> field :: Name -> String -> CExpr
> field v f = CField (CExpr (show v)) f

> lfield :: Name -> String -> LVar
> lfield v f = LField (LVar (show v)) f

> setField :: Name -> String -> CExpr -> CStmt
> setField v f = CAssign (LField (LVar (show v)) f)

> element :: CExpr -> Int -> CExpr
> element base n = CElem base (CInt n)

> setElem :: LVar -> Int -> CExpr -> CStmt
> setElem base n = CAssign (LElem base (CInt n))

> regRet :: CExpr
> regRet = CExpr "regs.ret"

> setRet :: CExpr -> CStmt
> setRet = CAssign (LVar "regs.ret")

> reg, stk :: Int -> CExpr
> reg = element (CExpr "regs.r")
> stk = element (CExpr "regs.sp")

> setReg, setStk :: Int -> CExpr -> CStmt
> setReg n = setElem (LVar "regs.r") n
> setStk n = setElem (LVar "regs.sp") n

> incrSp, decrSp :: Int -> CStmt
> incrSp n
>   | n >= 0 = CIncrBy (LVar "regs.sp") (CInt n)
>   | otherwise = CDecrBy (LVar "regs.sp") (CInt (-n))
> decrSp n = incrSp (-n)

> alloc :: CExpr
> alloc = asNode (CExpr "regs.hp")

> incrAlloc :: CExpr -> CStmt
> incrAlloc = CIncrBy (LVar "regs.hp")

> addr :: String -> CExpr
> addr = CAddr . CExpr

> asNode :: CExpr -> CExpr
> asNode = CCast nodePtrType

> goto :: String -> CStmt
> goto l = gotoExpr (CExpr l)

> gotoExpr :: CExpr -> CStmt
> gotoExpr l = CProcCall "GOTO" [l]

> funCall :: String -> [String] -> CExpr
> funCall f xs = CFunCall f (map CExpr xs)

> procCall :: String -> [String] -> CStmt
> procCall f xs = CProcCall f (map CExpr xs)

> wordCopy :: CExpr -> CExpr -> String -> CStmt
> wordCopy e1 e2 sz =
>   CProcCall "memcpy" [e1,e2,CExpr sz `CMul` CExpr "word_size"]

> rtsAssert :: CExpr -> CStmt
> rtsAssert e = CProcCall "ASSERT" [e]

> rtsAssertList :: [CExpr] -> CStmt
> rtsAssertList es = rtsAssert (foldr1 (flip CRel "&&") es)

> assertRel :: CExpr -> String -> CExpr -> CStmt
> assertRel x op y = rtsAssert (CRel x op y)

> add :: CExpr -> CExpr -> CExpr
> add (CInt 0) y = y
> add x (CInt 0) = x
> add x y = x `CAdd` y

> getFloat :: String -> CExpr -> [CStmt]
> getFloat v e =
>   [CLocalVar doubleType v Nothing,CProcCall "get_double_val" [CExpr v,e]]

> constRef :: String -> CExpr
> constRef = asNode . addr

> isTaggedPtr, isTaggedInt :: Name -> CExpr
> isTaggedPtr v = CFunCall "is_tagged_ptr" [var v]
> isTaggedInt v = CFunCall "is_tagged_int" [var v]

> nodeKind, nodeTag :: Name -> CExpr
> nodeKind v = field v "info->kind"
> nodeTag v = field v "info->tag"

\end{verbatim}
Frequently used types.
\begin{verbatim}

> boolType, intType, longType, uintType, ulongType, doubleType :: CType
> boolType = CType "boolean"
> intType = CType "int"
> longType = CType "long"
> uintType = CType "unsigned int"
> ulongType = CType "unsigned long"
> doubleType = CType "double"

> voidType, voidPtrType :: CType
> voidType = CType "void"
> voidPtrType = CPointerType voidType

> wordPtrType :: CType
> wordPtrType = CPointerType (CType "word")

> labelType, constLabelType :: CType
> labelType = CType "Label"
> constLabelType = CConstType "Label"

> nodeType, nodePtrType, nodeConstPtrType :: CType
> nodeType = CType "Node"
> nodePtrType = CPointerType nodeType
> nodeConstPtrType = CConstPointerType nodeType

> nodeInfoType, nodeInfoConstPtrType :: CType
> nodeInfoType = CType "NodeInfo"
> nodeInfoConstPtrType = CConstPointerType nodeInfoType

\end{verbatim}
We make use of some prelude entities in the generated code.
\begin{verbatim}

> prelName :: String -> Name
> prelName x = mangleQualified ("Prelude." ++ x)

> prelTrue, prelFalse :: Name
> prelTrue = prelName "True"
> prelFalse = prelName "False"

\end{verbatim}
