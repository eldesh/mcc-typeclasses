% -*- LaTeX -*-
% $Id: Modules.lhs 2189 2007-05-01 16:26:51Z wlux $
%
% Copyright (c) 1999-2007, Wolfgang Lux
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
> import Renaming(k0,rename,renameGoal)
> import PrecCheck(precCheck,precCheckGoal)
> import KindCheck(kindCheck,kindCheckGoal)
> import InstCheck(instCheck)
> import Deriving(derive)
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
> import Qual(qual1,qual2)
> import Desugar(desugar,goalModule)
> import Simplify(simplify)
> import DictTrans(dictTransModule,dictTransInterface)
> import Lift(lift)
> import qualified IL
> import ILTrans(ilTrans,ilTransIntf)
> import ILLift(liftProg)
> import DTransform(dTransform,dAddMain)
> import ILCompile(camCompile,camCompileData,fun)
> import qualified CamPP(ppModule)
> import CGen(genMain,genModule)
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
> import Utils

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
>     (mEnv,pEnv,tcEnv,iEnv,tyEnv,m) <- loadModule paths cm ws fn
>     let (tyEnv',trEnv,m',dumps) = transModule dbg tr tcEnv tyEnv m
>     liftErr $ mapM_ (doDump opts) dumps
>     let intf = exportInterface m pEnv tcEnv iEnv tyEnv'
>     liftErr $ unless (noInterface opts) (updateInterface fn intf)
>     mEnv' <- importDebugPrelude paths dbg fn (bindModule intf mEnv)
>     let (mEnv'',tyEnv'',m'',dumps) = dictTrans mEnv' tcEnv iEnv tyEnv' m'
>     liftErr $ mapM_ (doDump opts) dumps
>     let (il,dumps) = ilTransModule split dbg tyEnv'' trEnv m''
>     liftErr $ mapM_ (doDump opts) dumps
>     let (ccode,dumps) = genCodeModule mEnv'' il
>     liftErr $ mapM_ (doDump opts) dumps >>
>               writeCode (output opts) fn ccode
>   where paths = importPath opts
>         split = splitCode opts
>         dbg = debug opts
>         tr = if trusted opts then Trust else Suspect
>         cm = caseMode opts
>         ws = warn opts

> loadModule :: [FilePath] -> CaseMode -> [Warn] -> FilePath
>            -> ErrorT IO (ModuleEnv,PEnv,TCEnv,InstEnv,ValueEnv,Module Type)
> loadModule paths caseMode warn fn =
>   do
>     m <- liftErr (readFile fn) >>= okM . parseModule fn
>     mEnv <- loadInterfaces paths m
>     (pEnv,tcEnv,iEnv,tyEnv,m') <- okM $ checkModule mEnv m
>     liftErr $ mapM_ putErrLn $ warnModule caseMode warn m'
>     return (mEnv,pEnv,tcEnv,iEnv,tyEnv,m')

> parseModule :: FilePath -> String -> Error (Module ())
> parseModule fn s =
>   unlitLiterate fn s >>= liftM (importPrelude fn) . parseSource fn

> loadInterfaces :: [FilePath] -> Module a -> ErrorT IO ModuleEnv
> loadInterfaces paths (Module m _ is _) =
>   foldM (loadInterface paths [m]) emptyEnv
>         [P p m | ImportDecl p m _ _ _ <- is]

> checkModule :: ModuleEnv -> Module ()
>             -> Error (PEnv,TCEnv,InstEnv,ValueEnv,Module Type)
> checkModule mEnv (Module m es is ds) =
>   do
>     (pEnv,tcEnv,iEnv,tyEnv) <- importModules mEnv is
>     (tEnv,ds') <- typeSyntaxCheck m tcEnv iEnv ds
>     (vEnv,ds'') <- syntaxCheck m tEnv tyEnv ds'
>     es' <- checkExports m is tEnv vEnv es
>     let (k1,ds''') = rename k0 ds''
>     let (pEnv',tcEnv',tyEnv') = qualifyEnv1 mEnv is pEnv tcEnv tyEnv
>     (pEnv'',ds'''') <- precCheck m pEnv' (qual1 tEnv vEnv ds''')
>     tcEnv'' <- kindCheck m tcEnv' ds''''
>     iEnv' <- instCheck m tcEnv'' iEnv ds''''
>     (k2,deriv) <- liftM (rename k1) (derive m pEnv'' tcEnv'' iEnv' ds'''')
>     (tyEnv'',ds''''') <- typeCheck m tcEnv'' iEnv' tyEnv' (ds'''' ++ deriv)
>     let (pEnv''',tcEnv''',tyEnv''') =
>           qualifyEnv2 mEnv m pEnv'' tcEnv'' tyEnv''
>     return (pEnv''',tcEnv''',iEnv',tyEnv''',
>             Module m (Just es') is (qual2 tEnv vEnv ds'''''))

> warnModule :: CaseMode -> [Warn] -> Module Type -> [String]
> warnModule caseMode warn m =
>   caseCheck caseMode m ++ unusedCheck warn m ++
>   shadowCheck warn m ++ overlapCheck warn m

> transModule :: Bool -> Trust -> TCEnv -> ValueEnv -> Module Type
>             -> (ValueEnv,TrustEnv,Module Type,[(Dump,Doc)])
> transModule debug tr tcEnv tyEnv m = (tyEnv'',trEnv,simplified,dumps)
>   where trEnv = if debug then trustEnv tr m else emptyEnv
>         (desugared,tyEnv') = desugar tcEnv tyEnv m
>         (simplified,tyEnv'') = simplify tyEnv' trEnv desugared
>         dumps =
>           [(DumpRenamed,ppModule m),
>            (DumpTypes,ppTypes tcEnv (localBindings tyEnv)),
>            (DumpDesugared,ppModule desugared),
>            (DumpSimplified,ppModule simplified)]

> dictTrans :: ModuleEnv -> TCEnv -> InstEnv -> ValueEnv -> Module Type
>           -> (ModuleEnv,ValueEnv,Module Type,[(Dump,Doc)])
> dictTrans mEnv tcEnv iEnv tyEnv m = (mEnv',tyEnv',dict,dumps)
>   where mEnv' = fmap (dictTransInterface tcEnv tyEnv) mEnv
>         (tcEnv',tyEnv',dict) = dictTransModule tcEnv iEnv tyEnv m
>         dumps = [(DumpDict,ppModule dict)]

> ilTransModule :: Bool -> Bool -> ValueEnv -> TrustEnv -> Module Type
>               -> (Either IL.Module [IL.Module],[(Dump,Doc)])
> ilTransModule False debug tyEnv trEnv m = (Left il,dumps)
>   where (il,dumps) = ilTransModule1 id debug tyEnv trEnv m
> ilTransModule True debug tyEnv trEnv m = (Right il,concat (transpose dumps))
>   where (il,dumps) =
>           unzip $ map (ilTransModule1 id debug tyEnv trEnv) (splitModule m)

> ilTransModule1 :: (IL.Module -> IL.Module) -> Bool -> ValueEnv -> TrustEnv
>                -> Module Type -> (IL.Module,[(Dump,Doc)])
> ilTransModule1 debugAddMain debug tyEnv trEnv m = (ilDbg,dumps)
>   where (lifted,tyEnv',trEnv') = lift tyEnv trEnv m
>         il = ilTrans tyEnv' lifted
>         ilDbg
>           | debug = debugAddMain (dTransform (trustedFun trEnv') il)
>           | otherwise = il
>         dumps =
>           [(DumpLifted,ppModule lifted),
>            (DumpIL,ILPP.ppModule il)] ++
>           [(DumpTransformed,ILPP.ppModule ilDbg) | debug]

> genCodeModule :: ModuleEnv -> Either IL.Module [IL.Module]
>               -> (Either CFile [CFile],[(Dump,Doc)])
> genCodeModule mEnv (Left il) = (Left ccode,dumps)
>   where (ccode,dumps) = genCode (ilImports mEnv il) il
> genCodeModule mEnv (Right il) = (Right ccode,concat (transpose dumps))
>   where IL.Module m is ds = mergeILModules il
>         (ccode,dumps) =
>           unzip $ map (genCode (ilImports mEnv (IL.Module m is ds) ++ ds)) il

> genCode :: [IL.Decl] -> IL.Module -> (CFile,[(Dump,Doc)])
> genCode ds il = (ccode,dumps)
>   where ilNormal = liftProg il
>         cam = camCompile ilNormal
>         imports = camCompileData ds
>         ccode = genModule imports cam
>         dumps =
>           [(DumpNormalized,ILPP.ppModule ilNormal),
>            (DumpCam,CamPP.ppModule cam)]

> qualifyEnv1 :: ModuleEnv -> [ImportDecl] -> PEnv -> TCEnv -> ValueEnv
>            -> (PEnv,TCEnv,ValueEnv)
> qualifyEnv1 mEnv is pEnv tcEnv tyEnv =
>   (foldr (importEntities pEnv) pEnv' ms,
>    foldr (importEntities tcEnv) tcEnv' ms,
>    foldr (importEntities tyEnv) tyEnv' ms)
>   where ms = nub [(m,asM) | ImportDecl _ m False asM _ <- is]
>         (pEnv',tcEnv',_,tyEnv') =
>           foldl importInterfaceIntf initEnvs (map snd (envToList mEnv))
>         importEntities env (m,asM) env' =
>           foldr (uncurry (importTopEnv False m)) env'
>                 (moduleImports (fromMaybe m asM) env)

> qualifyEnv2 :: ModuleEnv -> ModuleIdent -> PEnv -> TCEnv -> ValueEnv
>            -> (PEnv,TCEnv,ValueEnv)
> qualifyEnv2 mEnv m pEnv tcEnv tyEnv =
>   (foldr (uncurry (globalBindTopEnv m)) pEnv' (localBindings pEnv),
>    foldr (uncurry (globalBindTopEnv m)) tcEnv' (localBindings tcEnv),
>    foldr (uncurry (bindTopEnv m)) tyEnv' (localBindings tyEnv))
>   where (pEnv',tcEnv',_,tyEnv') =
>           foldl importInterfaceIntf initEnvs (map snd (envToList mEnv))

> splitModule :: Module a -> [Module a]
> splitModule (Module m es is ds) = [Module m es is [d] | d <- ds, isCodeDecl d]
>   where isCodeDecl (DataDecl _ _ _ _ cs _) = not (null cs)
>         isCodeDecl (NewtypeDecl _ _ _ _ _ _) = True
>         isCodeDecl (TypeDecl _ _ _ _) = False
>         isCodeDecl (ClassDecl _ _ _ _ _) = True
>         isCodeDecl (InstanceDecl _ _ _ _ _) = True
>         isCodeDecl (BlockDecl d) = isValueDecl d

> mergeILModules :: [IL.Module] -> IL.Module
> mergeILModules ms = IL.Module m (concat iss) (concat dss)
>   where IL.Module m _ _ : _ = ms
>         (iss,dss) = unzip [(is,ds) | IL.Module _ is ds <- ms]

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

> compileGoal :: Options -> Maybe String -> [FilePath] -> ErrorT IO ()
> compileGoal opts g fns =
>   do
>     (mEnv,tcEnv,iEnv,tyEnv,_,g') <- loadGoal True paths cm ws g fns
>     let (vs,m',tyEnv') = goalModule dbg tyEnv m mainId g'
>     let (tyEnv'',trEnv,m'',dumps) = transModule dbg tr tcEnv tyEnv' m'
>     let trEnv' = if dbg then bindEnv mainId Suspect trEnv else trEnv
>     liftErr $ mapM_ (doDump opts) dumps
>     mEnv' <- importDebugPrelude paths dbg "" mEnv
>     let (mEnv'',tyEnv''',m''',dumps) = dictTrans mEnv' tcEnv iEnv tyEnv'' m''
>     liftErr $ mapM_ (doDump opts) dumps
>     let (il,dumps) = ilTransModule1 (dAddMain mainId) dbg tyEnv''' trEnv' m'''
>     liftErr $ mapM_ (doDump opts) dumps
>     let (ccode,dumps) = genCodeGoal mEnv'' (qualifyWith m mainId) vs il
>     liftErr $ mapM_ (doDump opts) dumps >>
>               writeGoalCode (output opts) ccode
>   where m = emptyMIdent
>         paths = importPath opts
>         dbg = debug opts
>         tr = if trusted opts then Trust else Suspect
>         cm = caseMode opts
>         ws = warn opts

> typeGoal :: Options -> String -> [FilePath] -> ErrorT IO ()
> typeGoal opts g fns =
>   do
>     (_,tcEnv,_,tyEnv,cx,Goal _ e _) <- loadGoal False paths cm ws (Just g) fns
>     liftErr $ print (ppQualType tcEnv (QualType cx (typeOf e)))
>   where paths = importPath opts
>         cm = caseMode opts
>         ws = warn opts

> loadGoal :: Bool -> [FilePath] -> CaseMode -> [Warn]
>          -> Maybe String -> [FilePath]
>          -> ErrorT IO (ModuleEnv,TCEnv,InstEnv,ValueEnv,Context,Goal Type)
> loadGoal forEval paths caseMode warn g fns =
>   do
>     (mEnv,ms) <- loadGoalModules paths fns
>     let m = last ms
>     (tcEnv,iEnv,tyEnv,cx,g') <-
>       okM $ maybe (return mainGoal) parseGoal g >>=
>             checkGoal forEval mEnv (map (importModule [m,preludeMIdent]) ms)
>     liftErr $ mapM_ putErrLn $ warnGoal caseMode warn g'
>     return (mEnv,tcEnv,iEnv,tyEnv,cx,g')
>   where p = first ""
>         mainGoal = Goal p (Variable () (qualify mainId)) []
>         importModule ms m = importDecl p m (m `notElem` ms)

> loadGoalModules :: [FilePath] -> [FilePath]
>                 -> ErrorT IO (ModuleEnv,[ModuleIdent])
> loadGoalModules paths fns =
>   do
>     mEnv <- loadInterface paths [] emptyEnv (P (first "") preludeMIdent)
>     (mEnv',ms) <- mapAccumM (loadGoalInterface paths) mEnv fns
>     return (mEnv',preludeMIdent:ms)

> loadGoalInterface :: [FilePath] -> ModuleEnv -> FilePath
>                   -> ErrorT IO (ModuleEnv,ModuleIdent)
> loadGoalInterface paths mEnv fn
>   | extension fn `elem` [srcExt,litExt,intfExt] || pathSep `elem` fn =
>       compileInterface paths [] mEnv (interfaceName fn)
>   | otherwise =
>       do
>         mEnv' <- loadInterface paths [] mEnv (P (first "") m)
>         return (mEnv',m)
>   where m = mkMIdent (components ('.':fn))
>         components [] = []
>         components (_:cs) =
>           case break ('.' ==) cs of
>             (cs',cs'') -> cs' : components cs''

> checkGoal :: Bool -> ModuleEnv -> [ImportDecl] -> Goal ()
>           -> Error (TCEnv,InstEnv,ValueEnv,Context,Goal Type)
> checkGoal forEval mEnv is g =
>   do
>     (pEnv,tcEnv,iEnv,tyEnv) <- importModules mEnv is
>     (tEnv,g') <- typeSyntaxCheckGoal tcEnv g
>     (vEnv,g'') <- syntaxCheckGoal tyEnv g'
>     let (k1,g''') = renameGoal k0 g''
>     let (pEnv',tcEnv',tyEnv') = qualifyEnv1 mEnv is pEnv tcEnv tyEnv
>     g'''' <- precCheckGoal pEnv' (qual1 tEnv vEnv g''')
>     (tyEnv'',cx,g''''') <- kindCheckGoal tcEnv' g'''' >>
>                          typeCheckGoal forEval tcEnv' iEnv tyEnv' g''''
>     let (_,tcEnv'',tyEnv''') =
>           qualifyGoalEnv forEval mEnv emptyMIdent pEnv' tcEnv' tyEnv''
>     return (tcEnv'',iEnv,tyEnv''',cx,qualifyGoal forEval tEnv vEnv g''''')

> qualifyGoalEnv :: Bool -> ModuleEnv -> ModuleIdent
>                -> PEnv -> TCEnv -> ValueEnv -> (PEnv,TCEnv,ValueEnv)
> qualifyGoalEnv True mEnv m pEnv tcEnv tyEnv =
>   qualifyEnv2 mEnv m pEnv tcEnv tyEnv
> qualifyGoalEnv False _ _ pEnv tcEnv tyEnv = (pEnv,tcEnv,tyEnv)

> qualifyGoal :: Bool -> TypeEnv -> FunEnv -> Goal a -> Goal a
> qualifyGoal True tEnv vEnv = qual2 tEnv vEnv
> qualifyGoal False _ _ = id

> warnGoal :: CaseMode -> [Warn] -> Goal Type -> [String]
> warnGoal caseMode warn g =
>   caseCheckGoal caseMode g ++ unusedCheckGoal warn g ++
>   shadowCheckGoal warn g ++ overlapCheckGoal warn g

> genCodeGoal :: ModuleEnv -> QualIdent -> Maybe [Ident] -> IL.Module
>             -> (CFile,[(Dump,Doc)])
> genCodeGoal mEnv qGoalId vs il = (mergeCFile ccode ccode',dumps)
>   where (ccode,dumps) = genCode (ilImports mEnv il) il
>         ccode' = genMain (fun qGoalId) (fmap (map name) vs)

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
>           | otherwise = importDecl (first fn) preludeMIdent False : is

> importDecl :: Position -> ModuleIdent -> Qualified -> ImportDecl
> importDecl p m q = ImportDecl p m q Nothing Nothing

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
> dumpHeader DumpDict = "Source code with dictionaries"
> dumpHeader DumpLifted = "Source code after lifting"
> dumpHeader DumpIL = "Intermediate code"
> dumpHeader DumpTransformed = "Transformed code" 
> dumpHeader DumpNormalized = "Intermediate code after normalization"
> dumpHeader DumpCam = "Abstract machine code"

\end{verbatim}
The function \texttt{ppTypes} is used for pretty-printing the types
from the type environment.
\begin{verbatim}

> ppTypes :: TCEnv -> [(Ident,ValueInfo)] -> Doc
> ppTypes tcEnv = vcat . map ppInfo
>   where ppInfo (c,DataConstructor _ _ (ForAll _ ty)) =
>           ppIDecl (mkDecl c ty) <+> text "-- data constructor"
>         ppInfo (c,NewtypeConstructor _ (ForAll _ ty)) =
>           ppIDecl (mkDecl c ty) <+> text "-- newtype constructor"
>         ppInfo (x,Value _ _ (ForAll _ ty)) = ppIDecl (mkDecl x ty)
>         mkDecl f ty =
>           IFunctionDecl undefined (qualify f) Nothing (fromQualType tcEnv ty)

\end{verbatim}
Various filename extensions.
\begin{verbatim}

> cExt = ".c"
> srcExt = ".curry"
> litExt = ".lcurry"
> intfExt = ".icurry"

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
