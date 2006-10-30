% -*- LaTeX -*-
% $Id: Modules.lhs 1989 2006-10-30 16:29:59Z wlux $
%
% Copyright (c) 1999-2006, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Modules.lhs}
\section{Modules}
This module controls the compilation of modules.
\begin{verbatim}

> module Modules(compileModule,compileGoal,typeGoal) where
> import Base
> import Unlit(unlit)
> import CurryParser(parseSource,parseInterface,parseGoal)
> import ImportSyntaxCheck(checkImports)
> import TypeSyntaxCheck(typeSyntaxCheck,typeSyntaxCheckGoal)
> import SyntaxCheck(syntaxCheck,syntaxCheckGoal)
> import ExportSyntaxCheck(checkExports)
> import Renaming(rename,renameGoal)
> import PrecCheck(precCheck,precCheckGoal)
> import KindCheck(kindCheck,kindCheckGoal)
> import TypeCheck(typeCheck,typeCheckGoal)
> import CaseCheck(caseCheck,caseCheckGoal)
> import UnusedCheck(unusedCheck,unusedCheckGoal)
> import ShadowCheck(shadowCheck,shadowCheckGoal)
> import OverlapCheck(overlapCheck,overlapCheckGoal)
> import IntfSyntaxCheck(intfSyntaxCheck)
> import IntfCheck(intfCheck)
> import IntfEquiv(fixInterface,intfEquiv)
> import Imports(importInterface,importInterfaceIntf,importUnifyData)
> import Exports(exportInterface)
> import Trust(trustEnv,trustEnvGoal)
> import Qual(Qual(..))
> import Desugar(desugar,desugarGoal)
> import Simplify(simplify)
> import Lift(lift)
> import qualified IL
> import ILTrans(ilTrans,ilTransIntf)
> import ILLift(liftProg)
> import DTransform(dTransform,dAddMain)
> import ILCompile(camCompile,camCompileData,fun)
> import qualified CamPP(ppModule)
> import CGen(genMain,genModule,genSplitModule)
> import CCode(CFile,mergeCFile)
> import CPretty(ppCFile)
> import CurryPP(ppModule,ppInterface,ppIDecl,ppGoal)
> import qualified ILPP(ppModule)
> import Options(Options(..),CaseMode(..),Warn(..),Dump(..))
> import Env
> import TopEnv
> import Combined
> import Error
> import IO
> import List
> import Maybe
> import Monad
> import PathUtils
> import Pretty
> import TypeTrans
> import Typing

\end{verbatim}
The function \texttt{compileModule} is the main entry point of this
module for compiling a Curry source module. It applies syntax and type
checking to the module and translates the code into one or more C code
files. The module's interface is updated when necessary.

The compiler automatically loads the prelude when compiling a module
-- except for the prelude itself -- by adding an appropriate import
declaration to the module.
\begin{verbatim}

> compileModule :: Options -> FilePath -> ErrorT IO ()
> compileModule opts fn =
>   do
>     (mEnv,tcEnv,tyEnv,m,intf) <- loadModule id paths cm ws fn
>     mEnv' <- importDebugPrelude paths dbg fn mEnv
>     let (ccode,dumps) = transModule split dbg tr mEnv' tcEnv tyEnv m
>     liftErr $ mapM_ (doDump opts) dumps >>
>               unless (noInterface opts) (updateInterface fn intf) >>
>               writeCode (output opts) fn ccode
>   where paths = importPath opts
>         split = splitCode opts
>         dbg = debug opts
>         tr = if trusted opts then Trust else Suspect
>         cm = caseMode opts
>         ws = warn opts

> loadModule :: (Module () -> Module ()) -> [FilePath] -> CaseMode -> [Warn]
>            -> FilePath
>            -> ErrorT IO (ModuleEnv,TCEnv,ValueEnv,Module Type,Interface)
> loadModule f paths caseMode warn fn =
>   do
>     m <- liftM f $ liftErr (readFile fn) >>= okM . parseModule fn
>     mEnv <- loadInterfaces paths m
>     (tcEnv,tyEnv,m',intf) <- okM $ checkModule mEnv m
>     liftErr $ mapM_ putErrLn $ warnModule caseMode warn m'
>     return (bindModule intf mEnv,tcEnv,tyEnv,m',intf)

> parseModule :: FilePath -> String -> Error (Module ())
> parseModule fn s =
>   unlitLiterate fn s >>= liftM (importPrelude fn) . parseSource fn

> loadInterfaces :: [FilePath] -> Module a -> ErrorT IO ModuleEnv
> loadInterfaces paths (Module m _ is _) =
>   foldM (loadInterface paths [m]) emptyEnv
>         [P p m | ImportDecl p m _ _ _ <- is]

> checkModule :: ModuleEnv -> Module a
>             -> Error (TCEnv,ValueEnv,Module Type,Interface)
> checkModule mEnv (Module m es is ds) =
>   do
>     (pEnv,tcEnv,iEnv,tyEnv) <- importModules mEnv is
>     (tEnv,iEnv',ds') <- typeSyntaxCheck m tcEnv iEnv ds
>     (vEnv,ds'') <- syntaxCheck m tyEnv ds'
>     es' <- checkExports m is tEnv vEnv es
>     (pEnv',ds''') <- precCheck m pEnv $ rename ds''
>     tcEnv' <- kindCheck m tcEnv ds'''
>     (tyEnv',ds'''') <- typeCheck m tcEnv' iEnv' tyEnv ds'''
>     let (pEnv'',tcEnv'',tyEnv'') = qualifyEnv mEnv m pEnv' tcEnv' tyEnv'
>     return (tcEnv'',tyEnv'',
>             Module m (Just es') is (qual tcEnv' tyEnv' ds''''),
>             exportInterface m es' pEnv'' tcEnv'' iEnv' tyEnv'')

> warnModule :: CaseMode -> [Warn] -> Module a -> [String]
> warnModule caseMode warn m =
>   caseCheck caseMode m ++ unusedCheck warn m ++
>   shadowCheck warn m ++ overlapCheck warn m

> transModule :: Bool -> Bool -> Trust -> ModuleEnv -> TCEnv -> ValueEnv
>             -> Module Type -> (Either CFile [CFile],[(Dump,Doc)])
> transModule split debug tr mEnv tcEnv tyEnv (Module m es is ds) =
>   (ccode,dumps)
>   where trEnv = trustEnv tr ds
>         (desugared,tyEnv') = desugar tcEnv tyEnv (Module m es is ds)
>         (simplified,tyEnv'') = simplify tyEnv' desugared
>         (lifted,tyEnv''',trEnv') = lift tyEnv'' trEnv simplified
>         il = ilTrans tyEnv''' lifted
>         ilDbg
>           | debug = dTransform (trustedFun trEnv') il
>           | otherwise = il
>         ilNormal = liftProg ilDbg
>         cam = camCompile ilNormal
>         imports = camCompileData (ilImports mEnv ilNormal)
>         ccode
>           | split = Right (genSplitModule imports cam)
>           | otherwise = Left (genModule imports cam)
>         dumps =
>           [(DumpRenamed,ppModule (Module m es is ds)),
>            (DumpTypes,ppTypes m (localBindings tyEnv)),
>            (DumpDesugared,ppModule desugared),
>            (DumpSimplified,ppModule simplified),
>            (DumpLifted,ppModule lifted),
>            (DumpIL,ILPP.ppModule il)] ++
>           [(DumpTransformed,ILPP.ppModule ilDbg) | debug ] ++
>           [(DumpNormalized,ILPP.ppModule ilNormal),
>            (DumpCam,CamPP.ppModule cam)]

> qualifyEnv :: ModuleEnv -> ModuleIdent -> PEnv -> TCEnv -> ValueEnv
>            -> (PEnv,TCEnv,ValueEnv)
> qualifyEnv mEnv m pEnv tcEnv tyEnv =
>   (foldr (uncurry (globalBindTopEnv m)) pEnv' (localBindings pEnv),
>    foldr (uncurry (globalBindTopEnv m)) tcEnv' (localBindings tcEnv),
>    foldr (uncurry (bindTopEnv m)) tyEnv' (localBindings tyEnv))
>   where (pEnv',tcEnv',_,tyEnv') =
>           foldl importInterfaceIntf initEnvs (map snd (envToList mEnv))

> ilImports :: ModuleEnv -> IL.Module -> [IL.Decl]
> ilImports mEnv (IL.Module _ is _) =
>   concat [ilTransIntf i | (m,i) <- envToList mEnv, m `elem` is]

> trustedFun :: TrustEnv -> QualIdent -> Bool
> trustedFun trEnv f = maybe True (Trust ==) (lookupEnv (unqualify f) trEnv)

> writeCode :: Maybe FilePath -> FilePath -> Either CFile [CFile] -> IO ()
> writeCode tfn sfn (Left cfile) = writeCCode ofn cfile
>   where ofn = fromMaybe (rootname sfn ++ cExt) tfn
> writeCode tfn sfn (Right cfiles) = zipWithM_ (writeCCode . mkFn) [1..] cfiles
>   where prefix = fromMaybe (rootname sfn) tfn
>         mkFn i = prefix ++ show i ++ cExt

> writeGoalCode :: Maybe FilePath -> CFile -> IO ()
> writeGoalCode tfn = writeCCode ofn
>   where ofn = fromMaybe (internalError "No filename for startup code") tfn

> writeCCode :: FilePath -> CFile -> IO ()
> writeCCode fn = writeFile fn . showln . ppCFile

> showln :: Show a => a -> String
> showln x = shows x "\n"

\end{verbatim}
A goal is compiled with respect to a given module. If no module is
specified, the Curry prelude is used. The source module has to be
parsed and type checked before the goal can be compiled. Otherwise,
compilation of a goal is similar to that of a module.
\begin{verbatim}

> compileGoal :: Options -> Maybe String -> Maybe FilePath -> ErrorT IO ()
> compileGoal opts g fn =
>   do
>     (mEnv,tcEnv,tyEnv,_,_,g') <- loadGoal paths cm ws g fn
>     mEnv' <- importDebugPrelude paths dbg "" mEnv
>     let (ccode,dumps) = transGoal dbg tr mEnv' tcEnv tyEnv g'
>     liftErr $ mapM_ (doDump opts) dumps >>
>               writeGoalCode (output opts) ccode
>   where paths = importPath opts
>         dbg = debug opts
>         tr = if trusted opts then Trust else Suspect
>         cm = caseMode opts
>         ws = warn opts

> typeGoal :: Options -> String -> Maybe FilePath -> ErrorT IO ()
> typeGoal opts g fn =
>   do
>     (_,_,tyEnv,m,cx,Goal _ e _) <-
>       loadGoal (importPath opts) (caseMode opts) (warn opts) (Just g) fn
>     liftErr $ print (ppQualType m (QualType cx (typeOf e)))

> loadGoal :: [FilePath] -> CaseMode -> [Warn] -> Maybe String -> Maybe FilePath
>          -> ErrorT IO (ModuleEnv,TCEnv,ValueEnv,ModuleIdent,Context,Goal Type)
> loadGoal paths caseMode warn g fn =
>   do
>     (mEnv,m,is) <- loadGoalModule paths g fn
>     (tcEnv,tyEnv,cx,g') <-
>       okM $ maybe (return mainGoal) parseGoal g >>= checkGoal mEnv is
>     liftErr $ mapM_ putErrLn $ warnGoal caseMode warn g'
>     return (mEnv,tcEnv,tyEnv,m,cx,g')
>   where mainGoal = Goal (first "") (Variable () (qualify mainId)) []

> loadGoalModule :: [FilePath] -> Maybe String -> Maybe FilePath
>                -> ErrorT IO (ModuleEnv,ModuleIdent,[ImportDecl])
> loadGoalModule paths (Just _) (Just fn) =
>   do
>     (mEnv,_,_,Module m _ is _,_) <-
>       loadModule transparent paths FreeMode [] fn
>     return (mEnv,m,is ++ [importDecl (first "") m])
>   where transparent (Module m _ is ds) = Module m Nothing is ds
> loadGoalModule paths Nothing (Just fn) =
>   do
>     (mEnv,m) <- compileInterface paths [] emptyEnv (interfaceName fn)
>     return (mEnv,emptyMIdent,[importDecl (first "") m])
> loadGoalModule paths _ Nothing =
>   do
>     mEnv <- loadInterface paths [] emptyEnv (P p m)
>     return (mEnv,emptyMIdent,[importDecl p m])
>   where p = first ""
>         m = preludeMIdent

> checkGoal :: ModuleEnv -> [ImportDecl] -> Goal a
>           -> Error (TCEnv,ValueEnv,Context,Goal Type)
> checkGoal mEnv is g =
>   do
>     (pEnv,tcEnv,iEnv,tyEnv) <- importModules mEnv is
>     g' <- typeSyntaxCheckGoal tcEnv g >>=
>           syntaxCheckGoal tyEnv >>=
>           precCheckGoal pEnv . renameGoal
>     (tyEnv',cx,g'') <- kindCheckGoal tcEnv g' >>
>                        typeCheckGoal tcEnv iEnv tyEnv g'
>     let (_,tcEnv',tyEnv'') = qualifyEnv mEnv emptyMIdent pEnv tcEnv tyEnv'
>     return (tcEnv',tyEnv'',cx,qual tcEnv' tyEnv' g'')

> warnGoal :: CaseMode -> [Warn] -> Goal a -> [String]
> warnGoal caseMode warn g =
>   caseCheckGoal caseMode g ++ unusedCheckGoal warn g ++
>   shadowCheckGoal warn g ++ overlapCheckGoal warn g

> transGoal :: Bool -> Trust -> ModuleEnv -> TCEnv -> ValueEnv -> Goal Type
>           -> (CFile,[(Dump,Doc)])
> transGoal debug tr mEnv tcEnv tyEnv g = (mergeCFile ccode ccode',dumps)
>   where m = emptyMIdent
>         goalId = mainId
>         qGoalId = qualifyWith m goalId
>         trEnv = bindEnv goalId Suspect (trustEnvGoal tr g)
>         (vs,desugared,tyEnv') = desugarGoal debug tcEnv tyEnv m goalId g
>         (simplified,tyEnv'') = simplify tyEnv' desugared
>         (lifted,tyEnv''',trEnv') = lift tyEnv'' trEnv simplified
>         il = ilTrans tyEnv''' lifted
>         ilDbg
>           | debug = dAddMain goalId (dTransform (trustedFun trEnv') il)
>           | otherwise = il
>         ilNormal = liftProg ilDbg
>         cam = camCompile ilNormal
>         imports = camCompileData (ilImports mEnv ilNormal)
>         ccode = genModule imports cam
>         ccode' = genMain (fun qGoalId) (fmap (map name) vs)
>         dumps =
>           [(DumpRenamed,ppGoal g),
>            (DumpTypes,ppTypes m (localBindings tyEnv)),
>            (DumpDesugared,ppModule desugared),
>            (DumpSimplified,ppModule simplified),
>            (DumpLifted,ppModule lifted),
>            (DumpIL,ILPP.ppModule il)] ++
>           [(DumpTransformed,ILPP.ppModule ilDbg) | debug ] ++
>           [(DumpNormalized,ILPP.ppModule ilNormal),
>            (DumpCam,CamPP.ppModule cam)]

\end{verbatim}
The function \texttt{importModules} brings the declarations of all
imported modules into scope in the current module.
\begin{verbatim}

> importModules :: ModuleEnv -> [ImportDecl]
>               -> Error (PEnv,TCEnv,InstEnv,ValueEnv)
> importModules mEnv ds =
>   do
>     ds' <- mapE checkImportDecl ds
>     let (pEnv,tcEnv,iEnv,tyEnv) = foldl importModule initEnvs ds'
>     return (pEnv,importUnifyData tcEnv,iEnv,tyEnv)
>   where checkImportDecl (ImportDecl p m q asM is) =
>           liftE (ImportDecl p m q asM)
>                 (checkImports (moduleInterface m mEnv) is)
>         importModule envs (ImportDecl _ m q asM is) =
>           importInterface (fromMaybe m asM) q is envs (moduleInterface m mEnv)

> moduleInterface :: ModuleIdent -> ModuleEnv -> Interface
> moduleInterface m mEnv =
>   fromMaybe (internalError "moduleInterface") (lookupEnv m mEnv)

> initEnvs :: (PEnv,TCEnv,InstEnv,ValueEnv)
> initEnvs = (initPEnv,initTCEnv,initIEnv,initDCEnv)

\end{verbatim}
The prelude is imported implicitly into every module that does not
import the prelude explicitly with an import declaration. Obviously,
no import declaration is added to the prelude itself.
\begin{verbatim}

> importPrelude :: FilePath -> Module a -> Module a
> importPrelude fn (Module m es is ds) = Module m es is' ds
>   where is'
>           | preludeMIdent `elem` (m : [m | ImportDecl _ m _ _ _ <- is]) = is
>           | otherwise = importDecl (first fn) preludeMIdent : is

> importDecl :: Position -> ModuleIdent -> ImportDecl
> importDecl p m = ImportDecl p m False Nothing Nothing

\end{verbatim}
The module \texttt{DebugPrelude} is loaded automatically when the
program is compiled for debugging. However, no explicit import is
added to the source code because \texttt{DebugPrelude} in turn imports
the prelude. Therefore, its loading is delayed until after the source
file has been checked.
\begin{verbatim}

> importDebugPrelude :: [FilePath] -> Bool -> FilePath -> ModuleEnv
>                    -> ErrorT IO ModuleEnv
> importDebugPrelude paths dbg fn mEnv
>   | dbg = loadInterface paths [] mEnv (P (first fn) debugPreludeMIdent)
>   | otherwise = return mEnv

\end{verbatim}
If an import declaration for a module is found, the compiler first
checks whether an import for the module is already pending. In this
case the module imports are cyclic, which is not allowed in Curry, and
the compilation is aborted. Next, the compiler checks whether the
module has been imported already. If so, nothing needs to be done,
otherwise the interface is searched in the import paths and loaded if
it is found.
\begin{verbatim}

> loadInterface :: [FilePath] -> [ModuleIdent] -> ModuleEnv -> P ModuleIdent
>               -> ErrorT IO ModuleEnv
> loadInterface paths ctxt mEnv (P p m)
>   | m `elem` ctxt = errorAt p (cyclicImport m (takeWhile (/= m) ctxt))
>   | isJust (lookupEnv m mEnv) = return mEnv
>   | otherwise =
>       liftErr (lookupInterface paths m) >>=
>       maybe (errorAt p (interfaceNotFound m))
>             (compileModuleInterface paths ctxt mEnv m)

> compileModuleInterface :: [FilePath] -> [ModuleIdent] -> ModuleEnv
>                        -> ModuleIdent -> FilePath -> ErrorT IO ModuleEnv
> compileModuleInterface paths ctxt mEnv m fn =
>   do
>     (mEnv',m') <- compileInterface paths ctxt mEnv fn
>     unless (m == m') (errorAt (first fn) (wrongInterface m m'))
>     return mEnv'

\end{verbatim}
After parsing an interface, all imported interfaces are recursively
loaded and entered into the interface's environment.

\ToDo{Avoid recursive loading of imported interfaces. All information
that is needed for compiling a module is present in the interfaces
that are imported directly from that module.}
\begin{verbatim}

> compileInterface :: [FilePath] -> [ModuleIdent] -> ModuleEnv
>                  -> FilePath -> ErrorT IO (ModuleEnv,ModuleIdent)
> compileInterface paths ctxt mEnv fn =
>   do
>     i <- liftErr (readFile fn) >>= okM . parseInterface fn
>     mEnv' <- loadIntfInterfaces paths ctxt mEnv i
>     Interface m is ds <- okM (checkInterface mEnv' i)
>     return (bindModule (Interface m is ds) mEnv',m)

> loadIntfInterfaces :: [FilePath] -> [ModuleIdent] -> ModuleEnv -> Interface
>                    -> ErrorT IO ModuleEnv
> loadIntfInterfaces paths ctxt mEnv (Interface m is _) =
>   foldM (loadInterface paths (m:ctxt)) mEnv [P p m | IImportDecl p m <- is]

> checkInterface :: ModuleEnv -> Interface -> Error Interface
> checkInterface mEnv (Interface m is ds) =
>   do
>     ds' <- intfSyntaxCheck ds
>     intfCheck m pEnv tcEnv tyEnv ds'
>     return (Interface m is ds')
>   where (pEnv,tcEnv,_,tyEnv) = foldl importModule initEnvs is
>         importModule envs (IImportDecl _ m) =
>           importInterfaceIntf envs (moduleInterface m mEnv)

\end{verbatim}
After checking a module successfully, the compiler may need to update
the module's interface file. The file will be updated only if the
interface has been changed or the file did not exist before.

The code below is a little bit tricky because we must make sure that the
interface file is closed before rewriting the interface -- even if it
has not been read completely. On the other hand, we must not apply
\texttt{hClose} too early. Note that there is no need to close the
interface explicitly if the interface check succeeds because the whole
file must have been read in this case. In addition, we do not update
the interface file in this case and therefore it doesn't matter when
the file is closed.
\begin{verbatim}

> updateInterface :: FilePath -> Interface -> IO ()
> updateInterface sfn i =
>   do
>     eq <- catch (matchInterface ifn i) (const (return False))
>     unless eq (writeInterface ifn i)
>   where ifn = interfaceName sfn

> matchInterface :: FilePath -> Interface -> IO Bool
> matchInterface ifn i =
>   do
>     h <- openFile ifn ReadMode
>     s <- hGetContents h
>     case parseInterface ifn s of
>       Ok i' | i `intfEquiv` fixInterface i' -> return True
>       _ -> hClose h >> return False

> writeInterface :: FilePath -> Interface -> IO ()
> writeInterface ifn = writeFile ifn . showln . ppInterface

> interfaceName :: FilePath -> FilePath
> interfaceName fn = rootname fn ++ intfExt

\end{verbatim}
The compiler searches for interface files in the import search path
using the extension \texttt{".icurry"}. Note that the current
directory is always searched first.
\begin{verbatim}

> lookupInterface :: [FilePath] -> ModuleIdent -> IO (Maybe FilePath)
> lookupInterface paths m = lookupFile (ifn : [catPath p ifn | p <- paths])
>   where ifn = foldr1 catPath (moduleQualifiers m) ++ intfExt

\end{verbatim}
Literate source files use the extension \texttt{".lcurry"}.
\begin{verbatim}

> unlitLiterate :: FilePath -> String -> Error String
> unlitLiterate fn s
>   | not (isLiterateSource fn) = return s
>   | null es = return s'
>   | otherwise = fail es
>   where (es,s') = unlit fn s

> isLiterateSource :: FilePath -> Bool
> isLiterateSource fn = litExt `isSuffixOf` fn

\end{verbatim}
The \texttt{doDump} function writes the selected information to the
standard output.
\begin{verbatim}

> doDump :: Options -> (Dump,Doc) -> IO ()
> doDump opts (d,x) =
>   when (d `elem` dump opts)
>        (print (text hd $$ text (replicate (length hd) '=') $$ x))
>   where hd = dumpHeader d

> dumpHeader :: Dump -> String
> dumpHeader DumpRenamed = "Module after renaming"
> dumpHeader DumpTypes = "Types"
> dumpHeader DumpDesugared = "Source code after desugaring"
> dumpHeader DumpSimplified = "Source code after simplification"
> dumpHeader DumpLifted = "Source code after lifting"
> dumpHeader DumpIL = "Intermediate code"
> dumpHeader DumpTransformed = "Transformed code" 
> dumpHeader DumpNormalized = "Intermediate code after normalization"
> dumpHeader DumpCam = "Abstract machine code"

\end{verbatim}
The function \texttt{ppTypes} is used for pretty-printing the types
from the type environment.
\begin{verbatim}

> ppTypes :: ModuleIdent -> [(Ident,ValueInfo)] -> Doc
> ppTypes m = vcat . map ppInfo
>   where ppInfo (c,DataConstructor _ (ForAll _ ty)) =
>           ppIDecl (mkDecl c ty) <+> text "-- data constructor"
>         ppInfo (c,NewtypeConstructor _ (ForAll _ ty)) =
>           ppIDecl (mkDecl c ty) <+> text "-- newtype constructor"
>         ppInfo (x,Value _ (ForAll _ ty)) = ppIDecl (mkDecl x ty)
>         mkDecl f ty = IFunctionDecl undefined (qualify f) (fromQualType m ty)

\end{verbatim}
Various filename extensions.
\begin{verbatim}

> cExt = ".c"
> intfExt = ".icurry"
> litExt = ".lcurry"

\end{verbatim}
Auxiliary functions. Unfortunately, hbc's \texttt{IO} module lacks a
definition of \texttt{hPutStrLn}.
\begin{verbatim}

> putErr :: String -> IO ()
> putErr = hPutStr stderr

> putErrLn :: String -> IO ()
> putErrLn s = putErr (unlines [s])

\end{verbatim}
Error messages.
\begin{verbatim}

> interfaceNotFound :: ModuleIdent -> String
> interfaceNotFound m = "Interface for module " ++ moduleName m ++ " not found"

> cyclicImport :: ModuleIdent -> [ModuleIdent] -> String
> cyclicImport m [] = "Recursive import for module " ++ moduleName m
> cyclicImport m ms =
>   "Cyclic import dependency between modules " ++ moduleName m ++
>     modules "" ms
>   where modules comma [m] = comma ++ " and " ++ moduleName m
>         modules _ (m:ms) = ", " ++ moduleName m ++ modules "," ms

> wrongInterface :: ModuleIdent -> ModuleIdent -> String
> wrongInterface m m' =
>   "Expected interface for " ++ show m ++ " but found " ++ show m'

\end{verbatim}
