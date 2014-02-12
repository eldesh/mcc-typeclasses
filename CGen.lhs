% -*- LaTeX -*-
% $Id: CGen.lhs 3151 2014-02-12 18:04:55Z wlux $
%
% Copyright (c) 1998-2013, Wolfgang Lux
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
The function \texttt{genMain} defines the main function of a Curry
program. This function first sets the global runtime system variables
that hold the default sizes of the heap, the stack, and the trail,
respectively, if non-standard sizes were specified for them at compile
time. Next, it initializes the runtime system by calling
\verb|curry_init|. Then, the goal of the Curry program is executed by
invoking either \verb|curry_exec| for a monadic goal or
\verb|curry_eval| for a non-monadic goal, and finally
\verb|curry_terminate| is called, which eventually prints the
statistics for the run. In case of a non-monadic goal, the main
function also defines the array holding the names of the goal's free
variables.
\begin{verbatim}

> genMain :: Name -> Maybe [String] -> [CTopDecl]
> genMain f fvs = CppInclude "curry.h" : mainFunction f fvs

> mainFunction :: Name -> Maybe [String] -> [CTopDecl]
> mainFunction f fvs =
>   [CMainFunc "main" ["argc","argv"]
>     (maybe [] (return . fvDecl "fv_names") fvs ++
>      [initVar v (defaultValue v) | v <- rtsVars] ++
>      [procCall "curry_init" ["&argc","argv"],
>       curry_main fvs f "fv_names" ["argc","argv"],
>       procCall "curry_exit" [],
>       CReturn (CInt 0)])]
>   where fvDecl v vs =
>           CStaticArray (CPointerType (CConstType "char")) v
>                        (map CInit (map CString vs ++ [CNull]))
>         initVar v d = CppCondStmts (defined d) [setVar (Name v) (CExpr d)] []
>         defaultValue v = "DEFAULT_" ++ map toUpper v
>         defined v = "defined(" ++ v ++ ")"
>         curry_main (Just _) = curry_eval
>         curry_main Nothing = const . curry_exec
>         curry_exec g args =
>           CProcCall "curry_exec" (constRef (constFunc g) : map CExpr args)
>         curry_eval g v args =
>           CProcCall "curry_eval" (addr (nodeInfo g) : map CExpr (v:args))

> rtsVars :: [String]
> rtsVars = [
>     "heapsize",
>     "stacksize",
>     "trailsize",
>     "print_fail",
>     "do_trace",
>     "show_stats"
>   ]

\end{verbatim}
\subsection{Modules}
The C code for a module is divided into code generated for the data
type declarations and code generated for the function definitions of
the module. Code generation is complicated by a few special cases that
need to be handled. In particular, the compiler must provide
definitions for the functions \texttt{@}$_n$ that implement
applications of a higher-order variable to $n$ arguments.\footnote{The
function name \texttt{@} is used instead of \texttt{@}$_1$.} These
functions cannot be predefined because there is no upper limit on the
arity of an application. Since these functions may be added in each
module, they must be declared as private -- i.e., \verb|static| --
functions.

In addition, the code generator preallocates the nodes for literal
constants globally. In fact, it preallocates all constants, but this
happens elsewhere. Constant constructors are defined together with
their node info and other constants are allocated separately for every
function because there is not much chance for them to be shared.
\begin{verbatim}

> genModule :: [(Name,[Name])] -> Module -> CFile
> genModule ts cam =
>   map CppInclude (nub ("curry.h" : [h | CCall (Just h) _ _ <- sts'])) ++
>   genTypes ts ds sts' ns ++
>   genFunctions ds fs sts' ns
>   where (_,ds,fs) = splitCam cam
>         sts = [st | (_,_,_,st) <- fs]
>         sts' = foldr linStmts [] sts
>         ns = foldr nodes [] sts

> linStmts :: Stmt -> [Stmt] -> [Stmt]
> linStmts st sts = st : linStmts' st sts

> linStmts' :: Stmt -> [Stmt] -> [Stmt]
> linStmts' (Return _) sts = sts
> linStmts' (Eval _) sts = sts
> linStmts' (Exec _ _) sts = sts
> linStmts' (CCall _ _ _) sts = sts
> linStmts' (Seq (_ :<- st1) st2) sts = linStmts st1 $ linStmts st2 sts
> linStmts' (Let _ st) sts = linStmts st sts
> linStmts' (Switch rf x cs) sts = foldr linStmts sts [st | Case _ st <- cs]
> linStmts' (Choice sts) sts' = foldr linStmts sts' sts

> switchTags :: [Stmt] -> [(Name,Int)]
> switchTags sts =
>   [(c,length vs) | Switch _ _ cs <- sts, Case (ConstrCase c vs) _ <- cs]

> nodes :: Stmt -> [Expr] -> [Expr]
> nodes (Return n) ns = n : ns
> nodes (Eval _) ns = ns
> nodes (Exec _ _) ns = ns
> nodes (CCall _ ty _) ns =
>   case ty of
>     Just TypeBool -> Constr prelTrue [] : Constr prelFalse [] : ns
>     Just _ -> ns
>     Nothing -> Constr prelUnit [] : ns
> nodes (Seq (_ :<- st1) st2) ns = nodes st1 $ nodes st2 ns
> nodes (Let ds st) ns = [n | Bind _ n <- ds] ++ nodes st ns
> nodes (Switch rf x cs) ns =
>   case rf of
>     Flex -> [node t | Case t _ <- cs] ++ ns'
>     Rigid ->
>       [Lit l | Case (LitCase l@(Integer i)) _ <- cs, not (fits32bits i)] ++
>       ns'
>   where ns' = foldr nodes ns [st | Case _ st <- cs]
>         node (LitCase l) = Lit l
>         node (ConstrCase c vs) = Constr c vs
> nodes (Choice sts) ns = foldr nodes ns sts

\end{verbatim}
\subsection{Data Types and Constants}
For every data type, the compiler defines an enumeration that assigns
tag numbers starting at zero to its data constructors from left to
right. The \verb|enum| declarations are not strictly necessary, but
simplify the code generator because it does not need to determine the
tag value of a constructor when it is used.

In addition to the tag enumerations, the compiler also defines node
info structures for every data constructor and preallocates constant
constructors and literal constants. Native integer constants as well
as multiple precision integer constants need to be allocated only if
they cannot be represented in $n-1$ bits where $n$ is the number of
bits per word of the target architecture. The generated code uses the
preprocessor macros \texttt{is\_large\_int} and
\texttt{is\_large\_int\_32\_64} defined in the runtime system (see
Sect.~\ref{sec:heap}) in order to determine whether allocation is
necessary. The latter macro is used only for multiple precision
integer constants that require more than 32 bits and less than 64
bits. On a 32-bit target this macro always yields true, whereas it
yields true on a 64-bit architecture only when the constant does not
fit into 63 bits.  Multiple precision integer constants that do not
fit into 64 bits are always allocated. Note that both macros always
return true if the system was configured with the
\texttt{--disable-pointer-tags} configuration option. Character
constants are encoded in pointers unless the system was configured
with the \texttt{--disable-pointer-tags} configuration option. In that
case, character constants with codes below 256, which are most
commonly used, are allocated in a table defined by the runtime system
and only constants with larger codes need to be preallocated in the
generated code. Multiple precision integer constants are preallocated
as well but they cannot be initialized statically because their
underlying representation is opaque. Instead, these constants are
initialized upon their first use.
\begin{verbatim}

> genTypes :: [(Name,[Name])] -> [(Name,[Name],[ConstrDecl])] -> [Stmt]
>          -> [Expr] -> [CTopDecl]
> genTypes ts ds sts ns =
>   -- imported data constructors
>   [tagDecl cs | (_,cs) <- ts, any (`elem` usedTs) cs] ++
>   [dataDecl c n | (c,n) <- usedCs] ++
>   -- local data declarations
>   [tagDecl (map snd3 cs) | (_,cs) <- ds'] ++
>   concat [dataDef ex vb c n | (ex,cs) <- ds', (vb,c,n) <- cs] ++
>   -- literal constants
>   literals [c | Lit c <- ns]
>   where ds' = [(existType vs cs,map constr cs) | (_,vs,cs) <- ds]
>         cs = concatMap snd ds'
>         cs' = [(c,n) | (_,c,n) <- cs]
>         usedTs = map fst (nub (switchTags sts) \\ cs')
>         usedCs = nub [(c,length vs) | Constr c vs <- ns] \\ cs'

> existType :: [Name] -> [ConstrDecl] -> Bool
> existType vs cs = any hasExistType cs
>   where hasExistType (ConstrDecl _ _ tys) = any hasExistVar tys
>         hasExistVar (TypeVar v) = v `notElem` vs
>         hasExistVar (TypeApp _ tys) = any hasExistVar tys
>         hasExistVar (TypeArr ty1 ty2) = hasExistVar ty1 || hasExistVar ty2

> constr :: ConstrDecl -> (Visibility,Name,Int)
> constr (ConstrDecl vb c tys) = (vb,c,length tys)

> tagDecl :: [Name] -> CTopDecl
> tagDecl cs = CEnumDecl [CConst (dataTag c) (Just n) | (c,n) <- zip cs [0..]]

> dataDecl :: Name -> Int -> CTopDecl
> dataDecl c n = head (dataDef undefined Exported c n)

> dataDef :: Bool -> Visibility -> Name -> Int -> [CTopDecl]
> dataDef ex vb c n
>   | n == 0 =
>       [CExternVarDecl nodeInfoConstPtrType (constNode c) | vb == Exported] ++
>       [CVarDef CPrivate nodeInfoType (nodeInfo c) (Just nodeinfo),
>        CVarDef (cVis vb) nodeInfoConstPtrType (constNode c)
>                (Just (CInit (addr (nodeInfo c))))]
>   | otherwise =
>       [CExternVarDecl nodeInfoType (nodeInfo c) | vb == Exported] ++
>       [CVarDef (cVis vb) nodeInfoType (nodeInfo c) (Just nodeinfo)]
>   where nodeinfo = CStruct (map CInit nodeinfo')
>         nodeinfo' =
>           [CExpr (if ex then "EAPP_KIND" else "CAPP_KIND"),CExpr (dataTag c),
>            closureNodeSize n,gcPointerTable,CString name,
>            CExpr "eval_whnf",noApply,noEntry,notFinalized]
>         name = snd $ splitQualified $ demangle c

> literals :: [Literal] -> [CTopDecl]
> literals cs =
>   map charConstant (nub [c | Char c <- cs]) ++
>   map intConstant (nub [i | Int i <- cs]) ++
>   map integerConstant (nub [i | Integer i <- cs]) ++
>   map floatConstant (nub [f | Float f <- cs])

> charConstant :: Char -> CTopDecl
> charConstant c =
>   CppCondDecls (CExpr "NO_POINTER_TAGS") (charNode c) (taggedChar c)
>   where charNode c
>           | ord c < 0x100 =
>               [CppDefine (constChar c)
>                          (asNode (CAdd (CExpr "char_table") (charCode c)))]
>           | otherwise =
>               [CVarDef CPrivate (CConstType "struct char_node") (constChar c)
>                  (Just (CStruct (map CInit [addr "char_info",charCode c]))),
>                CppDefine (constChar c) (constRef (constChar c))]
>         taggedChar c =
>           [CppDefine (constChar c) (CFunCall "tag_char" [charCode c])]
>         charCode c = int (ord c)

> intConstant :: Integer -> CTopDecl
> intConstant i =
>   CppCondDecls (CFunCall "is_large_int" [CInt i])
>     [CVarDef CPrivate (CConstType "struct int_node") (constInt i)
>              (Just (CStruct (map CInit [addr "int_info",CInt i]))),
>      CppDefine (constInt i) (constRef (constInt i))]
>     [CppDefine (constInt i) (CFunCall "tag_int" [CInt i])]

> integerConstant :: Integer -> CTopDecl
> integerConstant i =
>   CppCondDecls (isLargeInt [CInt i])
>     [CVarDef CPrivate (CType "struct bigint_node") (constInteger i) Nothing,
>      CppDefine (constInteger i) (constRef (constInteger i))]
>     [CppDefine (constInteger i) (CFunCall "tag_int" [CInt i])]
>   where isLargeInt
>           | fits32bits i = CFunCall "is_large_int"
>           | fits64bits i = CFunCall "is_large_int_32_64"
>           | otherwise = const (CInt 1)

> floatConstant :: Double -> CTopDecl
> floatConstant f =
>   CVarDef CPrivate (CConstType "struct float_node") (constFloat f)
>           (Just (CStruct (map CInit [addr "float_info",fval f])))
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
implement partial applications of data constructors. Furthermore, the
code for those functions \texttt{@}$_n$, which are used in the current
module, is generated.
\begin{verbatim}

> genFunctions :: [(Name,[Name],[ConstrDecl])]
>              -> [(Visibility,Name,[Name],Stmt)] -> [Stmt] -> [Expr]
>              -> [CTopDecl]
> genFunctions ds fs sts ns =
>   -- imported functions
>   map (instEntryDecl Exported) (nonLocal flexData) ++
>   map (entryDecl Exported) (nonLocal call) ++
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
>   [instEntryDecl vb c | (vb,c,_) <- flex'] ++
>   [instFunction vb c n | (vb,c,n) <- flex'] ++
>   -- (private) instantiation functions for literals
>   map litInstEntryDecl flexLits ++
>   map litInstFunction flexLits ++
>   -- (private) @ functions
>   map appEntryDecl appArgs ++
>   map appFunction appArgs ++
>   [entryDecl Private f | f <- ap] ++
>   concat [evalDef Private f (apArity f) | f <- apClos] ++
>   concat [lazyDef Private f (apArity f) | f <- apLazy] ++
>   concat [apFunction f (apArity f) | f <- ap] ++
>   -- auxiliary functions for partial applications of data constructors
>   [entryDecl Private c | (_,c,n) <- pcon', n > 0] ++
>   concat [pappDef vb c n | (vb,c,n) <- pcon', n > 0] ++
>   concat [fun0Def vb c n | (vb,c,n) <- con0', n > 0] ++
>   concat [conFunction Private c n | (_,c,n) <- pcon', n > 0] ++
>   -- local function declarations
>   [entryDecl vb f | (vb,f,_,_) <- fs] ++
>   concat [pappDef vb f n | (vb,f,n) <- papp', n > 0] ++
>   concat [evalDef vb f n | (vb,f,n) <- clos'] ++
>   concat [lazyDef vb f n | (vb,f,n) <- lazy'] ++
>   concat [fun0Def vb f n | (vb,f,n) <- fun0'] ++
>   concat [function vb f vs st | (vb,f,vs,st) <- fs]
>   where nonLocal =
>           filter (`notElem` [c | (_,c,_) <- cs] ++ [f | (_,f,_,_) <- fs])
>         papp = nub [f | Papp f _ <- ns]
>         (apCall,call) = partition isAp (nub [f | Exec f _ <- sts])
>         (apClos,clos) = partition isAp (nub [f | Closure f _ <- ns])
>         (apLazy,lazy) = partition isAp (nub [f | Lazy f _ <- ns])
>         fun0 = nub ([f | Papp f [] <- ns] ++ [f | Closure f [] <- ns])
>         ap = nub (apCall ++ apClos ++ apLazy)
>         appArgs = [1 .. maximum (0 : map (pred . apArity) ap)]
>         cs = [constr c | c <- concatMap thd3 ds]
>         fs' = [(vb,f,length vs) | (vb,f,vs,_) <- fs]
>         flex' = filter (used flexData) cs
>         pcon' = filter (used papp) cs
>         con0' = filter (used fun0) cs
>         papp' = filter (used papp) fs'
>         clos' = filter (used clos) fs'
>         lazy' = filter (used lazy) fs'
>         fun0' = filter (used fun0) fs'
>         pappArities = nub (map thd3 (pcon' ++ papp'))
>         closArities = nub (map apArity apClos ++ map thd3 clos')
>         lazyArities = nub (map apArity apLazy ++ map thd3 lazy')
>         ts = [t | Switch Flex _ cs <- sts, Case t _ <- cs]
>         flexLits = nub [l | LitCase l <- ts]
>         flexData = nub [c | ConstrCase c _ <- ts]
>         used _ (Exported,_,_) = True
>         used xs (Private,x,_) = x `elem` xs

> entryDecl :: Visibility -> Name -> CTopDecl
> entryDecl vb f = CFuncDecl (cVis vb) (cName f)

> applyEntryDecl :: Int -> Int -> CTopDecl
> applyEntryDecl m n = CFuncDecl CPrivate (applyFunc m n)

> evalEntryDecl :: Int -> CTopDecl
> evalEntryDecl n = CFuncDecl CPrivate (evalFunc n)

> lazyEntryDecl :: Int -> CTopDecl
> lazyEntryDecl n = CFuncDecl CPrivate (lazyFunc n)

> appEntryDecl :: Int -> CTopDecl
> appEntryDecl n = CFuncDecl CPrivate (appFunc n)

> instEntryDecl :: Visibility -> Name -> CTopDecl
> instEntryDecl vb c = CFuncDecl (cVis vb) (instFunc c)

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

> pappDef :: Visibility -> Name -> Int -> [CTopDecl]
> pappDef vb f n =
>   [pappDecl f | vb == Exported] ++
>   [CArrayDef (cVis vb) nodeInfoType (pappInfoTable f)
>              [pappInfo f i n | i <- [0..n-1]]]

> evalDef :: Visibility -> Name -> Int -> [CTopDecl]
> evalDef vb f n =
>   [evalDecl f | vb == Exported] ++
>   [CVarDef (cVis vb) nodeInfoType (nodeInfo f) (Just (funInfo f n))]

> lazyDef :: Visibility -> Name -> Int -> [CTopDecl]
> lazyDef vb f n =
>   [lazyDecl f | vb == Exported] ++
>   [CppCondDecls (CExpr "!COPY_SEARCH_SPACE")
>      [CArrayDef (cVis vb) nodeInfoType (lazyInfoTable f)
>                 (map (CStruct . map CInit) [suspinfo,queuemeinfo,indirinfo])]
>      [CArrayDef (cVis vb) nodeInfoType (lazyInfoTable f)
>                 [CStruct (map CInit suspinfo)]]]
>   where suspinfo =
>           [CExpr "SUSPEND_KIND",CExpr "EVAL_TAG",suspendNodeSize n,
>            gcPointerTable,CString (undecorate (demangle f)),
>            CExpr (lazyFunc n),noApply,CExpr (cName f),notFinalized]
>         queuemeinfo =
>           [CExpr "QUEUEME_KIND",CExpr "EVAL_TAG",suspendNodeSize n,
>            gcPointerTable,noName,CExpr "eval_queueMe",noApply,noEntry,
>            notFinalized]
>         indirinfo =
>           [CExpr "INDIR_KIND",CExpr "INDIR_TAG",suspendNodeSize n,
>            gcPointerTable,noName,CExpr "eval_indir",noApply,noEntry,
>            notFinalized]

> fun0Def :: Visibility -> Name -> Int -> [CTopDecl]
> fun0Def vb f n =
>   [fun0Decl f | vb == Exported] ++
>   [CVarDef (cVis vb) (CConstType "struct closure_node") (constFunc f)
>            (Just (CStruct [CInit (info f n),CStruct [CInit CNull]]))]
>   where info f n
>           | n == 0 = addr (nodeInfo f)
>           | otherwise = CExpr (pappInfoTable f)

> pappInfo :: Name -> Int -> Int -> CInitializer
> pappInfo f i n = CStruct (map CInit funinfo)
>   where funinfo =
>           [CExpr "PAPP_KIND",int (n - i),closureNodeSize i,gcPointerTable,
>            CString (undecorate (demangle f)),CExpr "eval_whnf",
>            CExpr (applyFunc i n),CExpr (cName f),notFinalized]

> funInfo :: Name -> Int -> CInitializer
> funInfo f n = CStruct (map CInit funinfo)
>   where funinfo =
>           [CExpr "FAPP_KIND",CExpr "EVAL_TAG",closureNodeSize n,
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

> function :: Visibility -> Name -> [Name] -> Stmt -> [CTopDecl]
> function vb f vs st = funcDefs vb (cpsFunction f vs st)

> applyFunction :: Int -> Int -> CTopDecl
> applyFunction m n = CFuncDef CPrivate (applyFunc m n) (applyCode m n)

> evalFunction :: Int -> CTopDecl
> evalFunction n = CFuncDef CPrivate (evalFunc n) (evalCode n)

> lazyFunction :: Int -> CTopDecl
> lazyFunction n = CFuncDef CPrivate (lazyFunc n) (lazyCode n)

> conFunction :: Visibility -> Name -> Int -> [CTopDecl]
> conFunction vb f n = function vb f vs (Return (Constr f vs))
>   where vs = [Name ('v' : show i) | i <- [1..n]]

> apFunction :: Name -> Int -> [CTopDecl]
> apFunction f n = funcDefs Private (cpsApplyFunction f vs)
>   where vs = [Name ('v' : show i) | i <- [1..n]]

> appFunction :: Int -> CTopDecl
> appFunction n = funcDef Private (cpsApply v vs)
>   where v:vs = [Name ('v' : show i) | i <- [0..n]]

> instFunction :: Visibility -> Name -> Int -> CTopDecl
> instFunction vb c n = funcDef vb (cpsInst v (ConstrCase c vs))
>   where v:vs = [Name ('v' : show i) | i <- [0..n]]

> litInstFunction :: Literal -> CTopDecl
> litInstFunction l = funcDef Private (cpsInst (Name "v0") (LitCase l))

> funcDefs :: Visibility -> CPSFunction -> [CTopDecl]
> funcDefs vb f =
>   map privFuncDecl ks ++ entryDef vb f : map (funcDef Private) ks
>   where ks = continuations f

> privFuncDecl :: CPSContinuation -> CTopDecl
> privFuncDecl (CPSContinuation f _ _ _) = CFuncDecl CPrivate (contName f)

> entryDef :: Visibility -> CPSFunction -> CTopDecl
> entryDef vb (CPSFunction f vs st) =
>   CFuncDef (cVis vb) (cName f)
>            (entryCode f vs ++ funCode f (vs,CPSReturn) st)

> funcDef :: Visibility -> CPSContinuation -> CTopDecl
> funcDef vb (CPSContinuation f vs ws st) =
>   CFuncDef (cVis vb) (contName f)
>            (funCode (name f) (vs,CPSCont f ws CPSReturn) st)
>   where name (CPSContFun f _) = f
>         name (CPSApp _) = Name ""
>         name (CPSInst _) = Name ""
>         name (CPSApply _) = Name ""
>         name CPSUpdate = Name ""

> entryCode :: Name -> [Name] -> [CStmt]
> entryCode f vs =
>   [procCall "C_STACK_CHECK" [cName f],
>    CProcCall "TRACE_FUN" [CString (undecorate (demangle f)),int (length vs)]]

\end{verbatim}
The compiler generates a C function from every CPS function. At the
beginning of a function, stack and heap checks are performed if
necessary. After the heap check, the function's arguments and local
variables are loaded from the argument registers and the stack. The
code for an alternative of a \texttt{switch} statement is similar
except that we avoid loading the matched variable again -- unless a
heap check is performed.
\begin{verbatim}

> funCode :: Name -> ([Name],CPSCont) -> CPSStmt -> [CStmt]
> funCode f vs st =
>   elimUnused (concatMap prepAlloc ds' ++ stackCheck vs st ++ heapCheck vs n ++
>               loadVars vs ++ constDefs consts ds ++ cCode f consts vs st)
>   where ds = concat dss
>         (tys,ds',dss) = allocs st
>         consts = constants dss
>         n = allocSize consts ds ds' tys

> caseCode :: Name -> ([Name],CPSCont) -> Name -> CPSTag -> CPSStmt -> [CStmt]
> caseCode f vs v t st =
>   concatMap prepAlloc ds' ++ stackCheck vs st ++ heapCheck vs n ++
>   skip (n == CInt 0) v (loadVars vs) ++ fetchArgs v t ++
>   constDefs consts ds ++ cCode f consts vs st
>   where ds = concat dss
>         (tys,ds',dss) = allocs st
>         consts = constants dss
>         n = allocSize consts ds ds' tys
>         skip True v = filter (\(CLocalVar _ v' _) -> show v /= v')
>         skip False _ = id

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
potential stack overflow when performing a tail call to a variable
instead of a known function.

The application entry points of partial application nodes use a
special calling convention where the additional arguments and the
return address are expected on the stack rather than in argument
registers and the return address register, respectively. This calling
convention is used so that the application entry points do not need to
shift the additional arguments to argument registers with higher
indices when loading the arguments from the partial application node
into their respective argument registers.
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

> evalCode :: Int -> [CStmt]
> evalCode n =
>   localVar v (Just (reg 0)) :
>   [setReg i (arg i) | i <- [0..n-1]] ++
>   [gotoExpr (field v "info->entry")]
>   where v = Name "clos"
>         arg = element (field v "c.args")

> lazyCode :: Int -> [CStmt]
> lazyCode n =
>   loadVars vs0 ++
>   CLocalVar labelType "entry" (Just (field v "info->entry")) :
>   [setReg i (arg i) | i <- [0..n-1]] ++
>   CIf (CRel (contAddr vs0 CPSReturn) "==" (CExpr "update"))
>       (localVar v' (Just (stk 0)) : lockIndir v v')
>       (stackCheck vs0 (CPSExec (CPSEval False v) k [v]) ++
>        saveVars vs0 (contVars vs0 [] [] k) ++
>        setRet (contAddr vs0 k) :
>        lock v) :
>   [goto "entry"]
>   where v = Name "susp"
>         v' = Name "que"
>         vs0 = ([v],CPSReturn)
>         k = CPSCont CPSUpdate [v] CPSReturn
>         arg = element (field v "c.args")

\end{verbatim}
At the beginning of a function or switch alternative, all arguments
and environment variables are loaded into local variables so that the
compiler can freely use the argument registers and stack slots. If the
return address is saved on the stack, it is loaded into a temporary
variable, too.

When saving the arguments and environment variables of a continuation
before leaving a function, we avoid saving variables that were loaded
from the same register or the same offset in the stack because the
optimizer of the C compiler may be unable to detect such redundant
operations. Note that \texttt{saveVars} never sets the return address
register, since this is not necessary when calling the return
continuation.
\begin{verbatim}

> loadVars :: ([Name],CPSCont) -> [CStmt]
> loadVars (vs,k) = loadArgs vs ++ loadEnv k
>   where loadVar f v i = localVar v (Just (f i))
>         loadRet ret = CLocalVar labelType (show retIpName) (Just ret)
>         loadArgs vs = zipWith (loadVar reg) vs [0..]
>         loadEnv CPSReturn = []
>         loadEnv (CPSCont _ ws _) =
>           zipWith (loadVar stk) ws [0..] ++
>           [loadRet (CCast labelType (stk (length ws)))]

> fetchArgs :: Name -> CPSTag -> [CStmt]
> fetchArgs _ (CPSLitCase _) = []
> fetchArgs v (CPSConstrCase _ vs) =
>   assertRel (CFunCall "closure_argc" [var v]) "==" (int (length vs)) :
>   zipWith fetchArg vs [0..]
>   where arg = element (field v "c.args")
>         fetchArg v i = localVar v (Just (arg i))
> fetchArgs _ CPSFreeCase = []
> fetchArgs _ CPSDefaultCase = []

> saveVars :: ([Name],CPSCont) -> ([Name],CPSCont) -> [CStmt]
> saveVars (vs0,k0) (vs,k) =
>   [incrSp d | d /= 0] ++
>   [setReg i v | (i,v0,v) <- zip3 [0..] vs0' vs', v0 /= v] ++
>   [setStk i w | (i,w0,w) <- zip3 [0..] ws0' ws, w0 /= w]
>   where d = length ws0 - length ws
>         vs' = map var vs
>         vs0' = map var vs0 ++ repeat (CExpr "")
>         ws = contFrame (vs0,k0) k
>         ws0 = contFrame (vs0,k0) k0
>         ws0' = if d >= 0 then drop d ws0 else replicate (-d) (CExpr "") ++ ws0

> updVar :: ([Name],CPSCont) -> Name -> CStmt
> updVar (vs,k) v =
>   case (elemIndex v vs,elemIndex v (envVars k)) of
>     (Just n,_) -> setReg n (var v)
>     (_,Just n) -> setStk n (var v)
>     _ -> error ("updVar " ++ show v)
>   where envVars CPSReturn = []
>         envVars (CPSCont _ ws _) = ws

\end{verbatim}
When computing the allocation requirements of a function, we have to
take nodes into account that are allocated explicitly in
\texttt{return} and \texttt{let} statements and implicitly for the
results of \texttt{ccall} statements, but can ignore nodes which are
allocated outside of the heap, i.e., all constant nodes. In addition,
we handle the dynamic allocation of partial application nodes by a
\texttt{CPSLetPapp} statement here.
\begin{verbatim}

> heapCheck :: ([Name],CPSCont) -> CExpr -> [CStmt]
> heapCheck (vs,_) n =
>   [CProcCall "CHECK_HEAP" [int (length vs),n] | n /= CInt 0]

> allocSize :: FM Name CExpr -> [Bind] -> [BindPapp] -> [CArgType] -> CExpr
> allocSize consts ds ds' tys =
>   foldr add (CInt 0)
>         ([ctypeSize ty | ty <- tys] ++
>          [nodeSize n | Bind v n <- ds, not (isConstant consts v)] ++
>          [partialNodeSize v vs | BindPapp _ v vs <- ds'])

> allocs :: CPSStmt -> ([CArgType],[BindPapp],[[Bind]])
> allocs (CPSLet ds st) = (tys,ds',ds:dss)
>   where (tys,ds',dss) = allocs st
> allocs (CPSLetC (BindC _ ty _) st) = (maybe id (:) ty tys,ds,dss)
>   where (tys,ds,dss) = allocs st
> allocs (CPSLetPapp d st) = (tys,d:ds,dss)
>   where (tys,ds,dss) = allocs st
> allocs (CPSLetCont _ st) = allocs st
> allocs _ = ([],[],[])

> nodeSize :: Expr -> CExpr
> nodeSize (Lit _) = CInt 0
> nodeSize (Constr _ vs) = closureNodeSize (length vs)
> nodeSize (Papp _ vs) = closureNodeSize (length vs)
> nodeSize (Closure _ vs) = closureNodeSize (length vs)
> nodeSize (Lazy _ vs) = suspendNodeSize (length vs)
> nodeSize Free = CExpr "variable_node_size"
> nodeSize (Var _) = CInt 0

> prepAlloc :: BindPapp -> [CStmt]
> prepAlloc (BindPapp _ v vs) =
>   [assertRel (nodeTag v) ">" (CInt (toInteger (length vs))),
>    CLocalVar uintType (argcVar v) (Just (CFunCall "closure_argc" [var v])),
>    CLocalVar uintType (szVar v) (Just (CFunCall "node_size" [var v]))]

> partialNodeSize :: Name -> [Name] -> CExpr
> partialNodeSize v vs = CExpr (szVar v) `CAdd` CInt (toInteger (length vs))

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
> closureNodeSize n = CFunCall "closure_node_size" [int n]
> suspendNodeSize n = CFunCall "suspend_node_size" [int n]

\end{verbatim}
The maximum stack depth of a function is simply the difference between
the number of variables saved on the stack when the function is
entered and the number of variables pushed onto the stack when calling
the continuation. In case of the various \texttt{CPSSwitch}
statements, each alternative is responsible for performing a stack
check.
\begin{verbatim}

> stackCheck :: ([Name],CPSCont) -> CPSStmt -> [CStmt]
> stackCheck (_,k) st = [CProcCall "CHECK_STACK" [int depth] | depth > 0]
>   where depth = stackDepth st - stackDepthCont k

> stackDepth :: CPSStmt -> Int
> stackDepth CPSFail = 0
> stackDepth (CPSExecCont k _) = stackDepthCont k
> stackDepth (CPSExec _ k _) = stackDepthCont k
> stackDepth (CPSLet _ st) = stackDepth st
> stackDepth (CPSLetC _ st) = stackDepth st
> stackDepth (CPSLetPapp _ st) = stackDepth st
> stackDepth (CPSLetCont _ st) = stackDepth st
> stackDepth (CPSSwitch _ _ _) = 0
> stackDepth (CPSSwitchVar _ _ _) = 0
> stackDepth (CPSSwitchArity _ _) = 0
> stackDepth (CPSChoice _ ks) = 1 + stackDepthCont (head ks)

> stackDepthCont :: CPSCont -> Int
> stackDepthCont k = length (contFrame undefined k)

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
>         init o (v,Var v') =
>           (o,(v,if v == v' then constRef "blackHole" else var v'))
>         init _ (v,n) = error ("internal error: constants.init" ++ show n)
>         constant = asNode . add (CExpr constArray) . int

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
> literal (Char c) = CExpr (constChar c)
> literal (Int i) = CExpr (constInt i)
> literal (Integer i) = CExpr (constInteger i)
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
>               CExpr (pappInfoTable f) `add` int (length vs) :
>               map arg vs ++ is
>         constInit (Bind v (Closure f vs)) is
>           | not (null vs) && isConstant consts v =
>               addr (nodeInfo f) : map arg vs ++ is
>         constInit _ is = is
>         arg v = fromJust (lookupFM v consts)

> allocNode :: FM Name CExpr -> Bind -> [CStmt]
> allocNode consts (Bind v n) =
>   case lookupFM v consts of
>     Just e -> [localVar v (Just e)]
>     Nothing ->
>       case n of
>         Lit c -> [localVar v (Just (literal c))]
>         Var v' -> [localVar v (Just (var v'))]
>         _ -> [localVar v (Just alloc),incrAlloc (nodeSize n)]

> allocPartial :: BindPapp -> [CStmt]
> allocPartial (BindPapp r v vs) =
>   [localVar r (Just alloc),incrAlloc (partialNodeSize v vs)]

> initNode :: FM Name CExpr -> Bind -> [CStmt]
> initNode _ (Bind _ (Lit l)) =
>   case l of
>     Integer i ->
>       [CppCondStmts (isLargeInt i)
>          [CProcCall initINTEGER [CExpr (constInteger i),CInt i]]
>          []]
>       where (isLargeInt,initINTEGER)
>               | fits32bits i = (\i -> "is_large_int("++show i++")","INIT_INTEGER32")
>               | fits64bits i = (\i -> "is_large_int_32_64("++show i++")","INIT_INTEGER64")
>               | otherwise = (const "1","INIT_INTEGER")
>     _ -> []
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
> initNode _ (Bind _ (Var _)) = []

> initInteger :: Name -> Integer -> CStmt
> initInteger v i =
>   CIf (CRel (field v "info") "==" CNull)
>       [setField v "info" (addr "bigint_info"),initMpz (field v "bi.mpz") i]
>       []
>   where initMpz v i
>           | fits32bits i = initMpzInt v i
>           | fits64bits i =
>               CppCondStmts condLP64 [initMpzInt v i] [initMpzString v i]
>           | otherwise = initMpzString v i
>         initMpzInt v i = CProcCall "mpz_init_set_si" [v,CInt i]
>         initMpzString v i =
>           CProcCall "mpz_init_set_str" [v,CString (show i),CInt 10]

> initConstr :: Name -> Name -> [Name] -> [CStmt]
> initConstr v c vs =
>   setField v "info" (addr (nodeInfo c)) : initArgs v "c.args" vs

> initPapp :: Name -> Name -> [Name] -> [CStmt]
> initPapp v f vs =
>   setField v "info" (CExpr (pappInfoTable f) `add` int (length vs)) :
>   initArgs v "c.args" vs

> initClosure :: Name -> Name -> [Name] -> [CStmt]
> initClosure v f vs =
>   setField v "info" (addr (nodeInfo f)) : initArgs v "c.args" vs

> initLazy :: Name -> Name -> [Name] -> [CStmt]
> initLazy v f vs =
>   setField v "info" (CExpr (lazyInfoTable f)) :
>   if null vs then
>     [setElem (lfield v "c.args") 0 CNull]
>   else
>     initArgs v "c.args" vs

> initFree :: Name -> [CStmt]
> initFree v =
>   [setField v "info" (CExpr "variable_info_table"),
>    setField v "v.wq" CNull,
>    setField v "v.cstrs" CNull]

> initPartial :: BindPapp -> [CStmt]
> initPartial (BindPapp r v vs) =
>   wordCopy (var r) (var v) (szVar v) :
>   CIncrBy (lfield r "info") (CInt (toInteger (length vs))) :
>   zipWith (initArg (lfield r "c.args") (CExpr (argcVar v))) [0..] vs
>   where initArg v1 n i v2 = CAssign (LElem v1 (n `add` int i)) (var v2)

> initArgs :: Name -> String -> [Name] -> [CStmt]
> initArgs v f vs = zipWith (initArg (lfield v f)) [0..] vs
>   where initArg v1 i v2 = setElem v1 i (var v2)

\end{verbatim}
Every abstract machine code statement is translated by its own
translation function.
\begin{verbatim}

> cCode :: Name -> FM Name CExpr -> ([Name],CPSCont) -> CPSStmt -> [CStmt]
> cCode f _ _ CPSFail = failAndBacktrack (undecorate (demangle f))
> cCode _ _ vs0 (CPSExecCont k vs) = execCont vs0 vs k
> cCode _ _ vs0 (CPSExec f k vs) = exec vs0 f vs k
> cCode f consts vs0 (CPSLet ds st) =
>   concatMap (allocNode consts) ds ++ concatMap (initNode consts) ds ++
>   cCode f consts vs0 st
> cCode f consts vs0 (CPSLetC d st) = cCall d ++ cCode f consts vs0 st
> cCode f consts vs0 (CPSLetPapp d st) =
>   allocPartial d ++ initPartial d ++ cCode f consts vs0 st
> cCode f consts vs0 (CPSLetCont _ st) = cCode f consts vs0 st
> cCode f _ vs0 (CPSSwitch tagged v cases) =
>   switchOnTerm f tagged vs0 v
>                [(t,caseCode f vs0 v t st) | CaseBlock t st <- cases]
> cCode f _ vs0 (CPSSwitchVar v st1 st2) = switchOnVar v sts1' sts2'
>   where sts1' = caseCode f vs0 v CPSFreeCase st1
>         sts2' = caseCode f vs0 v CPSFreeCase st2
> cCode f _ vs0 (CPSSwitchArity v sts) =
>   switchOnArity vs0 v (map (caseCode f vs0 v CPSDefaultCase) sts)
> cCode _ _ vs0 (CPSChoice v ks) = choice vs0 v ks

> execCont :: ([Name],CPSCont) -> [Name] -> CPSCont -> [CStmt]
> execCont vs0 vs k =
>   saveVars vs0 (contVars vs0 vs [] k) ++ [gotoExpr (contAddr vs0 k)]

> exec :: ([Name],CPSCont) -> CPSFun -> [Name] -> CPSCont -> [CStmt]
> exec vs0 f vs k =
>   saveVars vs0 vs0' ++
>   case f of
>     CPSEval tagged v ->
>       [tagSwitch vs0' v (taggedSwitch tagged) [cCase "EVAL_TAG" sts'],
>        gotoExpr ret]
>     _ -> sts'
>   where vs0' = contVars vs0 vs [] k
>         ret = contAddr vs0 k
>         sts' = [setRet ret | ret /= regRet] ++ [gotoExpr (entry f)]
>         taggedSwitch tagged v switch
>           | tagged = CIf (isTaggedPtr v) [switch] []
>           | otherwise = switch

> contVars :: ([Name],CPSCont) -> [Name] -> [Name] -> CPSCont
>          -> ([Name],CPSCont)
> contVars vs0 vs ws k = (vs ++ drop (length vs) (fst vs0),addVars ws k)
>   where addVars vs CPSReturn | null vs = CPSReturn
>         addVars vs (CPSCont f ws k) = CPSCont f (vs ++ ws) k

> entry :: CPSFun -> CExpr
> entry (CPSFun f) = CExpr (cName f)
> entry (CPSEval _ v) = field v "info->eval"
> entry CPSUnify = CExpr "bind_var"
> entry CPSDelay = CExpr "sync_var"

> contFrame :: ([Name],CPSCont) -> CPSCont -> [CExpr]
> contFrame _ CPSReturn = []
> contFrame vs0 (CPSCont _ ws k) =
>   map var ws ++ asNode (contAddr vs0 k) : contFrame vs0 k

> contAddr :: ([Name],CPSCont) -> CPSCont -> CExpr
> contAddr vs0 CPSReturn =
>   case snd vs0 of
>     CPSReturn -> regRet
>     CPSCont _ _ _ -> var retIpName
> contAddr _ (CPSCont f _ _) = contEntry f

> contEntry :: CPSContFun -> CExpr
> contEntry (CPSContFun f n) = CExpr (contName (CPSContFun f n))
> contEntry (CPSApp n) = CExpr (contName (CPSApp n))
> contEntry (CPSInst t) = CExpr (contName (CPSInst t))
> contEntry (CPSApply v) = field v "info->apply"
> contEntry CPSUpdate = CExpr (contName CPSUpdate)

> lock :: Name -> [CStmt]
> lock v =
>   [assertLazyNode v "SUSPEND_KIND",
>    CppCondStmts "!COPY_SEARCH_SPACE"
>      [CIf (CRel (CCast wordPtrType (var v)) "<" (CExpr "regs.hlim"))
>           [CProcCall "DO_SAVE" [var v,CExpr "q.wq"],
>            CIncrBy (lfield v "info") (CInt 1)]
>           [setField v "info" (CExpr "queueMe_info_table")]]
>      [setField v "info" (CExpr "queueMe_info_table")],
>    setField v "q.wq" CNull]

> lockIndir :: Name -> Name -> [CStmt]
> lockIndir v1 v2 =
>   [assertLazyNode v2 "QUEUEME_KIND",
>    CppCondStmts "!COPY_SEARCH_SPACE"
>      [CIf (CRel (CCast wordPtrType (var v1)) "<" (CExpr "regs.hlim"))
>           [CProcCall "DO_SAVE" [var v1,CExpr "n.node"],
>            CIncrBy (lfield v1 "info") (CInt 2)]
>           [setField v1 "info" (addr "indir_info")]]
>      [setField v1 "info" (addr "indir_info")],
>    setField v1 "n.node" (var v2)]

> assertLazyNode :: Name -> String -> CStmt
> assertLazyNode v kind =
>   rtsAssertList [isTaggedPtr v,CRel (nodeKind v) "==" (CExpr kind)]

> choice :: ([Name],CPSCont) -> Maybe Name -> [CPSCont] -> [CStmt]
> choice vs0 v ks =
>   CStaticArray constLabelType choices
>                (map (CInit . contAddr vs0) ks ++ [CInit CNull]) :
>   localVar ips (Just (asNode (CExpr choices))) :
>   saveVars vs0 vs0' ++
>   [CppCondStmts "!NO_STABILITY" (yieldCall v) [goto "regs.handlers->choices"]]
>   where ips = Name "_choice_ips"
>         choices = "_choices"
>         vs0' = contVars vs0 [] [ips] (head ks)
>         yieldCall (Just v) =
>           saveVars vs0' (contVars vs0' [v] [ips] (head ks)) ++
>           [setRet (CExpr "flex_yield_resume"),
>            goto "yield_delay_thread"]
>         yieldCall Nothing =
>           [setRet (CExpr "regs.handlers->choices"),
>            goto "yield_thread"]

> failAndBacktrack :: String -> [CStmt]
> failAndBacktrack msg =
>   [setReg 0 (asNode (CString msg)),
>    goto "regs.handlers->fail"]

\end{verbatim}
Code generation for \texttt{CPSSwitch} statements is a little bit more
complicated because matching literal constants requires two nested
switches. The outer switch matches the common tag and the inner switch
the literal's value. Furthermore, character and integer literals are
either encoded in the pointer or stored in a heap allocated node
depending on their value and the setting of the preprocessor constant
\texttt{NO\_POINTER\_TAGS}, which forces heap allocation of all
literals when set to a non-zero value.
\begin{verbatim}

> switchOnTerm :: Name -> Bool -> ([Name],CPSCont) -> Name -> [(CPSTag,[CStmt])]
>              -> [CStmt]
> switchOnTerm f tagged vs0 v cases =
>   tagSwitch vs0 v taggedSwitch (varCase ++ litCases ++ constrCases) :
>   head (dflts ++ [failAndBacktrack (undecorate (demangle f) ++ ": no match")])
>   where (lits,constrs,vars,dflts) = foldr partition ([],[],[],[]) cases
>         (chars,ints,integers,floats) = foldr litPartition ([],[],[],[]) lits
>         taggedSwitch v switch
>           | tagged && null chars && null ints && null integers =
>               CIf (isTaggedPtr v) [switch] []
>           | otherwise =
>               taggedCharSwitch v chars $
>               taggedIntSwitch v ints $
>               taggedIntegerSwitch v integers switch
>         varCase = map (cCase "LVAR_TAG") vars
>         litCases = map cCaseDefault $
>           [charCase | not (null chars)] ++
>           [intCase | not (null ints)] ++
>           [integerCase | not (null integers)] ++
>           [floatCase | not (null floats)]
>         charCase =
>           [CppCondStmts "NO_POINTER_TAGS"
>              [CProcCall "assert" [CFunCall "is_char_node" [var v]],
>               charSwitch (field v "ch.ch") chars,
>               CBreak]
>              [CProcCall "unexpected_tag"
>                         [CString (undecorate (demangle f)),nodeTag v]]]
>         intCase =
>           [CProcCall "assert" [CFunCall "is_int_node" [var v]],
>            intSwitch (field v "i.i") ints,
>            CBreak]
>         integerCase =
>           CProcCall "assert" [CFunCall "is_bigint_node" [var v]] :
>           integerSwitch (field v "bi.mpz") integers ++
>           [CBreak]
>         floatCase =
>           CProcCall "assert" [CFunCall "is_float_node" [var v]] :
>           floatSwitch v floats ++
>           [CBreak]
>         constrCases = [cCase (dataTag c) stmts | (c,stmts) <- constrs]
>         partition (t,stmts) ~(lits,constrs,vars,dflts) =
>           case t of
>              CPSLitCase l -> ((l,stmts) : lits,constrs,vars,dflts)
>              CPSConstrCase c _ -> (lits,(c,stmts) : constrs,vars,dflts)
>              CPSFreeCase -> (lits,constrs,stmts : vars,dflts)
>              CPSDefaultCase -> (lits,constrs,vars,stmts : dflts)
>         litPartition (Char c,stmts) ~(chars,ints,integers,floats) =
>           ((c,stmts):chars,ints,integers,floats)
>         litPartition (Int i,stmts) ~(chars,ints,integers,floats) =
>           (chars,(i,stmts):ints,integers,floats)
>         litPartition (Integer i,stmts) ~(chars,ints,integers,floats) =
>           (chars,ints,(i,stmts):integers,floats)
>         litPartition (Float f,stmts) ~(chars,ints,integers,floats) =
>           (chars,ints,integers,(f,stmts):floats)

> taggedCharSwitch :: Name -> [(Char,[CStmt])] -> CStmt -> CStmt
> taggedCharSwitch v chars stmt
>   | null chars = stmt
>   | otherwise =
>       CIf (isTaggedChar v)
>           [CppCondStmts "NO_POINTER_TAGS"
>              [CProcCall "curry_panic"
>                         [CString "impossible: is_tagged_char(%p)\n",var v]]
>              [charSwitch (CFunCall "untag_char" [var v]) chars]]
>           [stmt]

> taggedIntSwitch :: Name -> [(Integer,[CStmt])] -> CStmt -> CStmt
> taggedIntSwitch v ints stmt
>   | null ints = stmt
>   | otherwise =
>       CIf (isTaggedInt v)
>           [CppCondStmts "NO_POINTER_TAGS"
>              [CProcCall "curry_panic"
>                         [CString "impossible: is_tagged_int(%p)\n",var v]]
>              [intSwitch (CFunCall "untag_int" [var v]) ints]]
>           [stmt]

> taggedIntegerSwitch :: Name -> [(Integer,[CStmt])] -> CStmt -> CStmt
> taggedIntegerSwitch v integers stmt
>   | null ints64 = stmt
>   | otherwise =
>       CIf (isTaggedInt v)
>           [CppCondStmts "NO_POINTER_TAGS"
>              [CProcCall "curry_panic"
>                         [CString "impossible: is_tagged_int(%p)\n",var v]]
>              [condIntegerSwitch (CFunCall "untag_int" [var v]) ints32 ints64]]
>           [stmt]
>   where ints32 = filter (fits32bits . fst) ints64
>         ints64 = filter (fits64bits . fst) integers
>         condIntegerSwitch e ints32 ints64
>           | length ints32 == length ints64 = intSwitch e ints32
>           | null ints32 =
>               CppCondStmts condLP64 [intSwitch e ints64] []
>           | otherwise =
>               CppCondStmts condLP64 [intSwitch e ints64] [intSwitch e ints32]

> tagSwitch :: ([Name],CPSCont) -> Name -> (Name -> CStmt -> CStmt) -> [CCase]
>           -> CStmt
> tagSwitch vs0 v taggedSwitch cases =
>   CLoop [taggedSwitch v (CSwitch (nodeTag v) allCases),CBreak]
>   where allCases =
>           cCase "INDIR_TAG"
>                 [setVar v (field v "n.node"),updVar vs0 v,CContinue] :
>           cases

> charSwitch :: CExpr -> [(Char,[CStmt])] -> CStmt
> charSwitch e cases = CSwitch e [cCaseInt (ord c) stmts | (c,stmts) <- cases]

> intSwitch :: CExpr -> [(Integer,[CStmt])] -> CStmt
> intSwitch e cases = CSwitch e [CCase (CCaseInt i) stmts | (i,stmts) <- cases]

> integerSwitch :: CExpr -> [(Integer,[CStmt])] -> [CStmt]
> integerSwitch e cases = localVar k Nothing : foldr (match e) [] cases
>   where k = Name "k"
>         match e (i,stmts) rest
>           | fits32bits i =
>               [CIf (CRel (CFunCall "mpz_cmp_si" [e,CInt i]) "==" (CInt 0))
>                    stmts
>                    rest]
>           | otherwise =
>               [setVar k (CExpr (constInteger i)),
>                CIf (CRel (CFunCall "mpz_cmp" [e,field k "bi.mpz"]) "=="
>                          (CInt 0))
>                    stmts
>                    rest]

> floatSwitch :: Name -> [(Double,[CStmt])] -> [CStmt]
> floatSwitch v cases =
>   getFloat "d" (var v) ++ foldr (match (CExpr "d")) [] cases
>   where match v (f,stmts) rest = [CIf (CRel v "==" (CFloat f)) stmts rest]

\end{verbatim}
The idiosyncratic \texttt{CPSSwitchVar} statement is used for
distinguishing global and local free variable nodes. We assume that
neither the code for the global variable case (first alternative) nor
that for the local variable case (second alternative) falls through.
\begin{verbatim}

> switchOnVar :: Name -> [CStmt] -> [CStmt] -> [CStmt]
> switchOnVar v sts1 sts2 =
>   CIf (CRel (nodeKind v) "==" (CExpr "GVAR_KIND"))
>       (CProcCall "assert" [CFunCall "!is_local_space" [field v "g.spc"]] :
>        sts1)
>       [] :
>   sts2

\end{verbatim}
The \texttt{CPSSwitchArity} statement dispatches on the arity of a
partial application node. Recall that the first alternative,
corresponding to arity 0, applies to an unbound logical variable node
and that the last alternative acts as default case that is selected if
too few arguments are supplied.
\begin{verbatim}

> switchOnArity :: ([Name],CPSCont) -> Name -> [[CStmt]] -> [CStmt]
> switchOnArity vs0 v (sts0:stss) =
>   tagSwitch vs0 v taggedSwitch cases : last stss
>   where cases = cCase "LVAR_TAG" sts0 : zipWith cCaseInt [1..] (init stss)
>         taggedSwitch _ = id

\end{verbatim}
For a foreign function call, the generated code first unboxes all
arguments, then calls the function, and finally boxes the result of
the call. When taking the address of a foreign variable, the code
first loads this address into a temporary variable and then boxes it.
\begin{verbatim}

> cCall :: BindC -> [CStmt]
> cCall (BindC v ty cc) = cEval ty v' cc ++ box ty v (CExpr v')
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
> cAddr Nothing _ _ = []
> cAddr (Just ty) v x =
>   [CLocalVar (ctype ty) v (Just (CCast (ctype ty) (addr x)))]

> unbox :: CArgType -> String -> CExpr -> [CStmt]
> unbox TypeBool v e =
>   [CLocalVar (ctype TypeBool) v (Just (CField e "info->tag"))]
> unbox TypeChar v e =
>   [CLocalVar (ctype TypeChar) v (Just (CFunCall "char_val" [e]))]
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
> box Nothing v _ = [localVar v (Just (constRef (constNode prelUnit)))]
> box (Just TypeBool) v e =
>   [localVar v (Just (CCond e (const prelTrue) (const prelFalse)))]
>   where const = constRef . constNode
> box (Just TypeChar) v e =
>   [localVar v Nothing,
>    CppCondStmts "NO_POINTER_TAGS"
>      [CIf (CRel (CRel e ">=" (CInt 0)) "&&" (CRel e "<" (CInt 0x100)))
>        [setVar v (asNode (CExpr "char_table" `CAdd` e))]
>        [setVar v alloc,
>         setField v "info" (addr "char_info"),
>         setField v "ch.ch" e,
>         incrAlloc (ctypeSize TypeChar)]]
>      [setVar v (CFunCall "tag_char" [e])]]
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
>    setField v "info" (addr "float_info"),
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
unqualified name. In addition, we also drop the renaming keys that are
appended to the names of local variables and functions.
\begin{verbatim}

> undecorate :: String -> String
> undecorate cs =
>   case break ('_' ==) cs of
>     (cs', "") -> dropSuffix cs'
>     (cs', ('_':cs''))
>       | "debug#" `isPrefixOf` cs'' -> cs' ++ undecorate (drop 6 cs'')
>       | otherwise -> cs' ++ '_' : undecorate cs''
>   where dropSuffix cs =
>           case break (`elem` ".#") cs of
>             (cs',"") -> cs'
>             (cs','#':cs'')
>               | all isDigit cs'' -> cs'
>               | otherwise -> cs' ++ '#' : dropSuffix cs''
>             (cs','.':cs'')
>               | not (null cs'') && all isDigit cs'' -> cs'
>               | otherwise -> cs' ++ '.' : dropSuffix cs''

\end{verbatim}
In order to avoid some trivial name conflicts with the standard C
library, the names of all Curry functions are prefixed with two
underscores. The integer key of each CPS continuation function is
appended to its name to provide a unique name.

The names of the info vector for a data constructor application and
the info table for a function are constructed by appending the
suffixes \texttt{\_info} and \texttt{\_info\_table}, respectively, to
the name. The suffixes \texttt{\_const} and \texttt{\_function} are
used for constant constructors and functions, respectively.
\begin{verbatim}

> cVis :: Visibility -> CVisibility
> cVis Private = CPrivate
> cVis Exported = CPublic

> cName :: Name -> String
> cName x = "__" ++ show x

> cPrivName :: Name -> Int -> String
> cPrivName f n = cName f ++ '_' : show n

> contName :: CPSContFun -> String
> contName (CPSContFun f n) = cPrivName f n
> contName (CPSApp n) = appFunc n
> contName (CPSInst (LitCase l)) = litInstFunc l
> contName (CPSInst (ConstrCase c _)) = instFunc c
> --contName (CPSApply _) = error "internal error: contName (CPSApply)"
> contName CPSUpdate = "update"

> constArray :: String
> constArray = "constants"

> applyFunc :: Int -> Int -> String
> applyFunc m n = "apply_clos_" ++ show m ++ "_" ++ show n

> evalFunc, lazyFunc :: Int -> String
> evalFunc n = "eval_clos_" ++ show n
> lazyFunc n = "eval_lazy_" ++ show n

> appFunc :: Int -> String
> appFunc n = "apply" ++ show n

> instFunc :: Name -> String
> instFunc c = cName c ++ "_unify"

> litInstFunc :: Literal -> String
> litInstFunc (Char c) = constChar c ++ "_unify"
> litInstFunc (Int i) = constInt i ++ "_unify"
> litInstFunc (Integer i) = constInteger i ++ "_unify"
> litInstFunc (Float f) = constFloat f ++ "_unify"

> nodeInfo, pappInfoTable, lazyInfoTable :: Name -> String
> nodeInfo c = cName c ++ "_info"
> pappInfoTable f = cName f ++ "_papp_info_table"
> lazyInfoTable f = cName f ++ "_lazy_info_table"

> dataTag :: Name -> String
> dataTag c = cName c ++ "_tag"

> argcVar, szVar :: Name -> String
> argcVar v = show v ++ "_argc"
> szVar v = show v ++ "_sz"

> cArgVar, cRetVar :: Name -> String
> cArgVar v = "_carg" ++ "_" ++ show v
> cRetVar v = "_cret" ++ "_" ++ show v

> retIpName :: Name
> retIpName = Name "_ret_ip"

\end{verbatim}
The function \texttt{apArity} returns the arity of an application
function \texttt{@}$_n$. Note that \texttt{@}$_n$ has arity $n+1$
since $n$ denotes the arity of its first argument. Note the special
case for \texttt{@}, which is used instead of \texttt{@}$_1$.
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
>         arity _ = error "internal error: apArity"

> constChar :: Char -> String
> constChar c = "char_" ++ show (ord c)

> constInt :: Integer -> String
> constInt i = "int_" ++ mangle (show i)
>   where mangle ('-':cs) = 'M':cs
>         mangle cs = cs

> constInteger :: Integer -> String
> constInteger i = "integer_" ++ mangle (show i)
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
The functions \texttt{fits32bits} and \texttt{fits64bits} check
whether a signed integer literal fits into 32 and 64 bits,
respectively, and the string returned by function \texttt{condLP64} is
used as feature test for conditional compilation on a 64 bit target.
\begin{verbatim}

> fits32bits, fits64bits :: Integer -> Bool
> fits32bits i = -0x80000000 <= i && i <= 0x7fffffff
> fits64bits i = -0x8000000000000000 <= i && i <= 0x7fffffffffffffff

> condLP64 :: String
> condLP64 = "defined(_LP64) || defined(__LP64__)"
        
\end{verbatim}
Here are some convenience functions, which simplify the construction
of the abstract syntax tree.
\begin{verbatim}

> int :: Int -> CExpr
> int i = CInt (toInteger i)

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
> element base n = CElem base (int n)

> setElem :: LVar -> Int -> CExpr -> CStmt
> setElem base n = CAssign (LElem base (int n))

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

> incrSp :: Int -> CStmt
> incrSp n
>   | n >= 0 = CIncrBy (LVar "regs.sp") (CInt n')
>   | otherwise = CDecrBy (LVar "regs.sp") (CInt (-n'))
>   where n' = toInteger n

> alloc :: CExpr
> alloc = asNode (CExpr "regs.hp")

> incrAlloc :: CExpr -> CStmt
> incrAlloc = CIncrBy (LVar "regs.hp")

> addr :: String -> CExpr
> addr = CAddr . CExpr

> asNode :: CExpr -> CExpr
> asNode = CCast nodePtrType

> cCase :: String -> [CStmt] -> CCase
> cCase l = CCase (CCaseLabel l)

> cCaseInt :: Int -> [CStmt] -> CCase
> cCaseInt i = CCase (CCaseInt (toInteger i))

> cCaseDefault :: [CStmt] -> CCase
> cCaseDefault = CCase CCaseDefault

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

> isTaggedPtr, isTaggedInt, isTaggedChar :: Name -> CExpr
> isTaggedPtr v = CFunCall "is_tagged_ptr" [var v]
> isTaggedInt v = CFunCall "is_tagged_int" [var v]
> isTaggedChar v = CFunCall "is_tagged_char" [var v]

> nodeKind, nodeTag :: Name -> CExpr
> nodeKind v = field v "info->kind"
> nodeTag v = field v "info->tag"

\end{verbatim}
Frequently used types.
\begin{verbatim}

> intType, longType, uintType, doubleType :: CType
> intType = CType "int"
> longType = CType "long"
> uintType = CType "unsigned int"
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

> prelUnit, prelTrue, prelFalse :: Name
> prelUnit = prelName "()"
> prelTrue = prelName "True"
> prelFalse = prelName "False"

\end{verbatim}
