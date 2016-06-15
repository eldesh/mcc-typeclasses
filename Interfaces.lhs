% -*- LaTeX -*-
% $Id: Interfaces.lhs 3220 2016-06-15 22:32:30Z wlux $
%
% Copyright (c) 1999-2015, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Interfaces.lhs}
\section{Interfaces}
This module controls loading of interfaces imported by a module or
goal.
\begin{verbatim}

> module Interfaces(ModuleEnv,moduleInterface,importedInterfaces,
>                   loadInterfaces,loadGoalInterfaces,
>                   importModuleIdents,importModules,
>                   qualifyEnv1,qualifyEnv2,updateInterface) where
> import Base
> import Combined
> import Curry
> import CurryParser
> import CurryPP
> import CurryUtils
> import Env
> import Error
> import Files
> import IdentInfo
> import Imports
> import IntfCheck
> import IntfEquiv
> import IntfQual
> import IntfSyntaxCheck
> import InstInfo
> import IO
> import List
> import Maybe
> import Monad
> import PathUtils
> import Position
> import PrecInfo
> import TopEnv
> import TypeInfo
> import Utils
> import ValueInfo

\end{verbatim}
The interfaces of all imported modules are maintained in a global
environment.
\begin{verbatim}

> type ModuleEnv = Env ModuleIdent Interface

> bindModule :: Interface -> ModuleEnv -> ModuleEnv
> bindModule (Interface m is ds) = bindEnv m (Interface m is ds)

> unbindModule :: ModuleIdent -> ModuleEnv -> ModuleEnv
> unbindModule = unbindEnv

> moduleInterface :: ModuleIdent -> ModuleEnv -> Interface
> moduleInterface m mEnv =
>   fromMaybe (internalError "moduleInterface") (lookupEnv m mEnv)

> importedInterfaces :: [ModuleIdent] -> ModuleEnv -> [ModuleIdent]
> importedInterfaces ms mEnv = filter (isJust . flip lookupEnv mEnv) ms

\end{verbatim}
The compiler loads the interfaces of all modules imported by the
compiled module. Since interfaces are closed, it is not necessary to
recursively load the interfaces of those modules whose entities are
reexported by the imported modules.
\begin{verbatim}

> loadInterfaces :: [ImportPath] -> ModuleIdent -> [P ModuleIdent]
>                -> ErrorT IO ModuleEnv
> loadInterfaces paths m ms =
>   do
>     okM $ sequenceE_ [errorAt p (cyclicImport m) | P p m' <- ms, m == m']
>     mEnv <- foldM (loadInterface True paths) emptyEnv ms
>     okM $ checkInterfaces mEnv
>     return (sanitizeInterfaces m mEnv)

> loadInterface :: Bool -> [ImportPath] -> ModuleEnv -> P ModuleIdent
>               -> ErrorT IO ModuleEnv
> loadInterface fullPath paths mEnv (P p m) =
>   case lookupEnv m mEnv of
>     Just _ -> return mEnv
>     Nothing ->
>       liftErr (lookupInterface fullPath paths m) >>=
>       maybe (errorAt p (interfaceNotFound m)) (compileModuleInterface mEnv m)

> compileModuleInterface :: ModuleEnv -> ModuleIdent -> FilePath
>                        -> ErrorT IO ModuleEnv
> compileModuleInterface mEnv m fn =
>   do
>     (m',i) <- compileInterface fn
>     unless (m == m') (errorAt (first fn) (wrongInterface m m'))
>     return (bindModule i mEnv)

\end{verbatim}
A goal is compiled in an environment where the exported entities of
the Prelude and of all modules specified on the command line are in
scope with unqualified imports. In addition the exported entities of
all standard library modules are in scope with qualified imports.
Modules can be specified on the command line either by their file name
or by their module name. To avoid loading the interfaces of all
standard library modules when compiling a goal, we collect the module
identifiers that are used in the goal expression and only load the
interfaces of those standard library modules that appear in that list.
\begin{verbatim}

> loadGoalInterfaces :: [ImportPath] -> [P ModuleIdent] -> [FilePath]
>                    -> [ModuleIdent] -> ErrorT IO (ModuleEnv,[ModuleIdent])
> loadGoalInterfaces paths ms fns ms' =
>   do
>     mEnv <- foldM (loadInterface False paths) emptyEnv ms
>     (mEnv',ms'') <- mapAccumM (loadGoalInterface paths) mEnv fns
>     mEnv'' <- foldM (loadLibInterface paths) mEnv' ms'
>     okM $ checkInterfaces mEnv''
>     return (mEnv'',ms'')

> loadGoalInterface :: [ImportPath] -> ModuleEnv -> FilePath
>                   -> ErrorT IO (ModuleEnv,ModuleIdent)
> loadGoalInterface paths mEnv fn
>   | extension fn `elem` moduleExts || pathSep `elem` fn =
>       do
>         (m,i) <- compileInterface (interfName fn)
>         return (bindModule i mEnv,m)
>   | otherwise =
>       do
>         mEnv' <- loadInterface True paths mEnv (P (first "") m)
>         return (mEnv',m)
>   where m = mkMIdent (components ('.':fn))
>         components [] = []
>         components (_:cs) =
>           case break ('.' ==) cs of
>             (cs',cs'') -> cs' : components cs''

> loadLibInterface :: [ImportPath] -> ModuleEnv -> ModuleIdent
>                  -> ErrorT IO ModuleEnv
> loadLibInterface paths mEnv m =
>   case lookupEnv m mEnv of
>     Just _ -> return mEnv
>     Nothing ->
>       liftErr (lookupInterface False paths m) >>=
>       maybe (return mEnv) (compileModuleInterface mEnv m)

\end{verbatim}
The compiler looks for interface files in the import search path
using the extension \texttt{".icurry"}. Note that the current
directory is always searched first unless we look only for standard
library interfaces.
\begin{verbatim}

> lookupInterface :: Bool -> [ImportPath] -> ModuleIdent -> IO (Maybe FilePath)
> lookupInterface fullPath paths m
>   | fullPath = lookupFile (filesInPath (ImpDir "" : paths) ifn)
>   | otherwise = lookupFile (filesInPath [LibDir p | LibDir p <- paths] ifn)
>   where ifn = foldr1 catPath (moduleQualifiers m) ++ icurryExt

\end{verbatim}
After parsing an interface, the compiler applies syntax checking to
the interface. This is possible because interface files are
self-contained.
\begin{verbatim}

> compileInterface :: FilePath -> ErrorT IO (ModuleIdent,Interface)
> compileInterface fn =
>   do
>     Interface m is ds <- liftErr (readFile fn) >>= okM . parseInterface fn
>     ds' <- okM $ intfSyntaxCheck ds
>     return (m,Interface m is (qualIntf m ds'))

\end{verbatim}
After all interface files have been loaded, the compiler checks that
reexported definitions in the interfaces are consistent and compatible
with their original definitions where the latter are available.
\begin{verbatim}

> checkInterfaces :: ModuleEnv -> Error ()
> checkInterfaces mEnv = mapE_ checkInterface is
>   where (ms,is) = unzip (envToList mEnv)
>         (pEnv,tcEnv,iEnv,tyEnv) = foldl (importInterfaceIntf ms) initEnvs is
>         checkInterface (Interface m _ ds) =
>           intfCheck m pEnv tcEnv iEnv tyEnv ds

\end{verbatim}
When mutually recursive modules are compiled, the imported interfaces
may contain entities that are supposed to be defined in the current
module. These entities must not be imported into the current module
because they might be in conflict with their actual definitions in the
current module.
\begin{verbatim}

> sanitizeInterfaces :: ModuleIdent -> ModuleEnv -> ModuleEnv
> sanitizeInterfaces m mEnv = fmap (sanitizeInterface m) (unbindModule m mEnv)

> sanitizeInterface :: ModuleIdent -> Interface -> Interface
> sanitizeInterface m (Interface m' is' ds') =
>   Interface m' is' (filter ((Just m /=) . fst . splitQualIdent . entity) ds')

\end{verbatim}
The functions \texttt{importModuleIdents} and \texttt{importModules}
bring the declarations of all imported modules into scope for the
current module or goal expression.
\begin{verbatim}

> importModuleIdents :: ModuleEnv -> [ImportDecl] -> (TypeEnv,InstSet,FunEnv)
> importModuleIdents mEnv ds = (importUnifyData tEnv,iSet,importUnifyData vEnv)
>   where (tEnv,iSet,vEnv) = foldl importModule initIdentEnvs ds
>         importModule envs (ImportDecl _ m q asM is) =
>           importIdents (fromMaybe m asM) q is envs (moduleInterface m mEnv)

> importModules :: ModuleEnv -> [ImportDecl] -> (PEnv,TCEnv,InstEnv,ValueEnv)
> importModules mEnv ds = (pEnv,tcEnv,iEnv,tyEnv)
>   where (pEnv,tcEnv,iEnv,tyEnv) = foldl importModule initEnvs ds
>         importModule envs (ImportDecl _ m q asM is) =
>           importInterface (fromMaybe m asM) q is envs (moduleInterface m mEnv)

\end{verbatim}
The function \texttt{qualifyEnv1} brings the declarations of all
loaded modules into scope with qualified names and in addition brings
those entities into scope with unqualified names for which an
unqualified import is present. The function \texttt{qualifyEnv2}
brings the declarations of all loaded modules with their qualified
names into scope and in additions adds all local entities into scope
with their qualified names. Note that \texttt{qualifyEnv1} respects
local module aliases for qualified imports whereas
\texttt{qualifyEnv2} ignores them.
\begin{verbatim}

> qualifyEnv1 :: ModuleEnv -> [ImportDecl] -> PEnv -> TCEnv -> ValueEnv
>             -> (PEnv,TCEnv,ValueEnv)
> qualifyEnv1 mEnv is pEnv tcEnv tyEnv =
>   (foldr (importEntities pEnv) pEnv' ms,
>    foldr (importEntities tcEnv) tcEnv' ms,
>    foldr (importEntities tyEnv) tyEnv' ms)
>   where ms = nub [(m,asM) | ImportDecl _ m False asM _ <- is]
>         (ms',is') = unzip (envToList mEnv)
>         (pEnv',tcEnv',_,tyEnv') = foldl (importInterfaceIntf ms') initEnvs is'
>         importEntities env (m,asM) env' =
>           foldr (uncurry (importTopEnv False m)) env'
>                 (moduleBindings (fromMaybe m asM) env)

> qualifyEnv2 :: ModuleEnv -> ModuleIdent -> PEnv -> TCEnv -> ValueEnv
>            -> (PEnv,TCEnv,ValueEnv)
> qualifyEnv2 mEnv m pEnv tcEnv tyEnv =
>   (foldr (uncurry (globalBindTopEnv m)) pEnv' (localBindings pEnv),
>    foldr (uncurry (globalBindTopEnv m)) tcEnv' (localBindings tcEnv),
>    foldr (uncurry (bindTopEnv m)) tyEnv' (localBindings tyEnv))
>   where (ms,is) = unzip (envToList mEnv)
>         (pEnv',tcEnv',_,tyEnv') = foldl (importInterfaceIntf ms) initEnvs is

\end{verbatim}
After successfully checking a module, the compiler may need to update
the module's interface file. The file will be updated only if the
interface has been changed or the file did not exist before.

The code below is a little bit tricky because we must make sure that
the interface file is closed before rewriting the interface -- even if
it has not been read completely because \texttt{intfEquiv} has found a
difference. On the other hand, we must not apply \texttt{hClose} too
early. Note that there is no need to close the interface explicitly if
the interface check succeeds because the whole file must have been
read in this case. In addition, we do not update the interface file in
this case and therefore it doesn't matter when the file is closed.
\begin{verbatim}

> updateInterface :: FilePath -> Interface -> IO ()
> updateInterface sfn i =
>   do
>     eq <- IO.catch (matchInterface ifn i) (const (return False))
>     unless eq (writeInterface ifn i)
>   where ifn = interfName sfn

> matchInterface :: FilePath -> Interface -> IO Bool
> matchInterface ifn i =
>   do
>     h <- openFile ifn ReadMode
>     s <- hGetContents h
>     case parseInterface ifn s of
>       Ok i' | i `intfEquiv` fixInterface i' -> return True
>       _ -> hClose h >> return False

> writeInterface :: FilePath -> Interface -> IO ()
> writeInterface ifn = writeFile ifn . showLn . ppInterface

\end{verbatim}
Auxiliary definitions.
\begin{verbatim}

> initIdentEnvs :: (TypeEnv,InstSet,FunEnv)
> initIdentEnvs = (initTEnv,initISet,initVEnv)

> initEnvs :: (PEnv,TCEnv,InstEnv,ValueEnv)
> initEnvs = (initPEnv,initTCEnv,initIEnv,initDCEnv)

\end{verbatim}
Error messages.
\begin{verbatim}

> interfaceNotFound :: ModuleIdent -> String
> interfaceNotFound m = "Interface for module " ++ moduleName m ++ " not found"

> cyclicImport :: ModuleIdent -> String
> cyclicImport m = "Module " ++ moduleName m ++ " imports itself"

> wrongInterface :: ModuleIdent -> ModuleIdent -> String
> wrongInterface m m' =
>   "Expected interface for " ++ show m ++ " but found " ++ show m'

\end{verbatim}
