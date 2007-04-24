% -*- LaTeX -*-
% $Id: CurryDeps.lhs 2167 2007-04-24 13:46:23Z wlux $
%
% Copyright (c) 2002-2006, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CurryDeps.lhs}
\section{Building Programs}
This module implements the functions to compute the dependency
information between Curry modules. This is used to create Makefile
dependencies and to update programs composed of multiple modules.
\begin{verbatim}

> module CurryDeps where
> import Ident
> import Unlit
> import CurrySyntax hiding(Interface(..))
> import CurryParser(parseHeader)
> import SCC
> import Env
> import List
> import Maybe
> import Monad
> import Error
> import IO
> import PathUtils

> data Source = Source FilePath [ModuleIdent]
>             | Interface FilePath
>             | Unknown
>             deriving (Eq,Ord,Show)
> type SourceEnv = Env ModuleIdent Source

\end{verbatim}
The module has two entry points. The function \texttt{buildScript}
computes either a build or clean script for a module while
\texttt{makeDepend} computes dependency rules for inclusion into a
Makefile.
\begin{verbatim}

> buildScript :: Bool -> Bool -> Bool -> [FilePath] -> [FilePath]
>             -> Maybe FilePath -> FilePath -> IO [String]
> buildScript clean debug linkAlways paths libPaths target fn =
>   do
>     (ms,es) <-
>       fmap (flattenDeps . sortDeps)
>            (deps paths (filter (`notElem` paths) libPaths) emptyEnv fn)
>     when (null es) (putStr (makeScript clean debug linkAlways outputFile ms))
>     return es
>   where outputFile
>           | extension fn `elem` moduleExts ++ [oExt] = Nothing
>           | otherwise = target `mplus` Just fn
>         makeScript clean = if clean then makeCleanScript else makeBuildScript

> makeDepend :: [FilePath] -> [FilePath] -> Maybe FilePath -> [FilePath]
>            -> IO ()
> makeDepend paths libPaths target ms =
>   foldM (deps paths (filter (`notElem` paths) libPaths)) emptyEnv ms >>=
>   maybe putStr writeFile target . makeDeps

> deps :: [FilePath] -> [FilePath] -> SourceEnv -> FilePath -> IO SourceEnv
> deps paths libPaths mEnv fn
>   | e `elem` sourceExts = sourceDeps paths libPaths (mkMIdent [r]) mEnv fn
>   | e == icurryExt = return mEnv
>   | e == oExt = targetDeps paths libPaths mEnv r
>   | otherwise = targetDeps paths libPaths mEnv fn
>   where r = rootname fn
>         e = extension fn

> targetDeps :: [FilePath] -> [FilePath] -> SourceEnv -> FilePath
>            -> IO SourceEnv
> targetDeps paths libPaths mEnv fn =
>   lookupFile [fn ++ e | e <- sourceExts] >>=
>   maybe (return (bindEnv m Unknown mEnv)) (sourceDeps paths libPaths m mEnv)
>   where m = mkMIdent [fn]

\end{verbatim}
The following functions are used to lookup files related to a given
module. Source files for targets are looked up in the current
directory only. Two different search paths are used to look up
imported modules, the first is used to find source modules, whereas
the library path is used only for finding matching interface files. As
the compiler does not distinguish these paths, we actually check for
interface files in the source paths as well.

Note that the functions \texttt{buildScript} and \texttt{makeDepend}
already remove all directories that are included in the both search
paths from the library paths in order to avoid scanning such
directories more than twice.
\begin{verbatim}

> lookupModule :: [FilePath] -> [FilePath] -> ModuleIdent
>              -> IO (Maybe FilePath)
> lookupModule paths libPaths m =
>   lookupFile ([p `catPath` fn ++ e | p <- "" : paths, e <- moduleExts] ++
>               [p `catPath` fn ++ icurryExt | p <- libPaths])
>   where fn = foldr1 catPath (moduleQualifiers m)

\end{verbatim}
In order to compute the dependency graph, source files for each module
need to be looked up. When a source module is found, its header is
parsed in order to determine the modules that it imports, and
dependencies for these modules are computed recursively. The prelude
is added implicitly to the list of imported modules except for the
prelude itself. Any errors reported by the parser are ignored.
\begin{verbatim}

> moduleDeps :: [FilePath] -> [FilePath] -> SourceEnv -> ModuleIdent
>            -> IO SourceEnv
> moduleDeps paths libPaths mEnv m =
>   case lookupEnv m mEnv of
>     Just _ -> return mEnv
>     Nothing ->
>       do
>         mbFn <- lookupModule paths libPaths m
>         case mbFn of
>           Just fn
>             | icurryExt `isSuffixOf` fn ->
>                 return (bindEnv m (Interface fn) mEnv)
>             | otherwise -> sourceDeps paths libPaths m mEnv fn
>           Nothing -> return (bindEnv m Unknown mEnv)

> sourceDeps :: [FilePath] -> [FilePath] -> ModuleIdent -> SourceEnv
>            -> FilePath -> IO SourceEnv
> sourceDeps paths libPaths m mEnv fn =
>   do
>     s <- readFile fn
>     case parseHeader fn (unlitLiterate fn s) of
>       Ok (Module m' _ is _) ->
>         let ms = imports m' is in
>         foldM (moduleDeps paths libPaths) (bindEnv m (Source fn ms) mEnv) ms
>       Errors _ -> return (bindEnv m (Source fn []) mEnv)

> imports :: ModuleIdent -> [ImportDecl] -> [ModuleIdent]
> imports m ds = nub $
>   [preludeMIdent | m /= preludeMIdent] ++ [m | ImportDecl _ m _ _ _ <- ds]

> unlitLiterate :: FilePath -> String -> String
> unlitLiterate fn
>   | lcurryExt `isSuffixOf` fn = snd . unlit fn
>   | otherwise = id

\end{verbatim}
It is quite straight forward to generate Makefile dependencies from
the dependency environment. In order for these dependencies to work,
the Makefile must include a rule
\begin{verbatim}
.SUFFIXES: .lcurry .curry .icurry
.o.icurry: @echo interface $@ not found, remove $< and recompile; exit 1
\end{verbatim}
This dependency rule introduces an indirect dependency between a
module and its interface. In particular, the interface may be updated
when the module is recompiled and a new object file is generated but
it does not matter if the interface is out-of-date with respect to the
object code.
\begin{verbatim}

> makeDeps :: SourceEnv -> String
> makeDeps mEnv =
>   unlines (filter (not . null) (map (depsLine . snd) (envToList mEnv)))
>   where depsLine (Source fn ms) =
>           objectName False fn ++ ": " ++ fn ++ " " ++
>           unwords (filter (not . null) (map interf ms))
>         depsLine (Interface _) = []
>         depsLine Unknown = []
>         interf m = maybe [] interfFile (lookupEnv m mEnv)
>         interfFile (Source fn _) = interfName fn
>         interfFile (Interface fn) = fn
>         interfFile Unknown = ""

\end{verbatim}
If we want to compile the program instead of generating Makefile
dependencies the environment has to be sorted topologically. Note
that the dependency graph should not contain any cycles.
\begin{verbatim}

> sortDeps :: SourceEnv -> [[(ModuleIdent,Source)]]
> sortDeps = scc (modules . fst) (imports . snd) . envToList
>   where modules m = [m]
>         imports (Source _ ms) = ms
>         imports (Interface _) = []
>         imports Unknown = []

> flattenDeps :: [[(ModuleIdent,Source)]] -> ([(ModuleIdent,Source)],[String])
> flattenDeps [] = ([],[])
> flattenDeps (dep:deps) =
>   case dep of
>     [] -> (ms',es')
>     [m] -> (m:ms',es')
>     _ -> (ms',cyclicError (map fst dep) : es')
>   where (ms',es') = flattenDeps deps

> cyclicError :: [ModuleIdent] -> String
> cyclicError (m:ms) =
>   "Cylic import dependency between modules " ++ show m ++ rest ms
>   where rest [m] = " and " ++ show m
>         rest (m:ms) = ", " ++ show m ++ rest' ms
>         rest' [m] = ", and " ++ show m
>         rest' (m:ms) = ", " ++ show m ++ rest' ms

\end{verbatim}
The function \texttt{makeBuildScript} returns a shell script that
rebuilds a program given a sorted list of module informations. The
script uses the commands \verb|compile| and \verb|link| to build the
program. They should be defined to reasonable values in the
environment where the script is executed. The script deliberately uses
the \verb|-e| shell option so that the script is terminated upon the
first error.
\begin{verbatim}

> makeBuildScript :: Bool -> Bool -> Maybe FilePath -> [(ModuleIdent,Source)]
>                 -> String
> makeBuildScript debug linkAlways target mEnv =
>   unlines ("set -e" : concatMap (compCommands . snd) mEnv ++
>            maybe [] linkCommands target)
>   where compCommands (Source fn ms) =
>           [newer ofn (fn : catMaybes (map interf ms)) ++ " || \\",compile fn]
>           where ofn = objectName debug fn
>         compCommands (Interface _) = []
>         compCommands Unknown = []
>         linkCommands fn
>           | linkAlways = [link fn ms os]
>           | otherwise = [newer fn os ++ " || \\", link fn ms os]
>           where ms = catMaybes (map modul mEnv)
>                 os = reverse (catMaybes (map (object . snd) mEnv))
>         newer fn fns = unwords ("$CURRY_PATH/newer" : fn : fns)
>         compile fn = unwords ["compile","-c",fn,"-o",objectName debug fn]
>         link fn ms os = unwords ("link" : "-o" : fn : ms ++ os)
>         modul (_,Source fn _) = Just ("-M" ++ fn)
>         modul (m,Interface _) = Just ("-M" ++ moduleName m)
>         modul (_,Unknown) = Nothing
>         interf m =
>           case lookup m mEnv of
>             Just (Source fn _) -> Just (interfName fn)
>             Just (Interface fn) -> Just fn
>             Just Unknown -> Nothing
>             Nothing -> Nothing
>         object (Source fn _) = Just (objectName debug fn)
>         object (Interface _) = Nothing
>         object Unknown = Nothing

\end{verbatim}
The function \texttt{makeCleanScript} returns a shell script that
removes all compiled files for a module. The script uses the command
\verb|remove| to delete the files. It should be defined to a
reasonable value in the environment where the script is executed.
\begin{verbatim}

> makeCleanScript :: Bool -> Bool -> Maybe FilePath -> [(ModuleIdent,Source)]
>                 -> String
> makeCleanScript debug _ target mEnv =
>   unwords ("remove" : foldr (files . snd) (maybeToList target) mEnv)
>   where d = if debug then 2 else 0
>         files (Source fn _) fs =
>           drop d [interfName fn,objectName False fn,objectName True fn] ++ fs
>         files (Interface _) fs = fs
>         files Unknown fs = fs

\end{verbatim}
The functions \texttt{interfName} and \texttt{objectName} compute the
name of an interface and object file for a source module. Note that
output files are always created in the same directory as the source
file.
\begin{verbatim}

> interfName :: FilePath -> FilePath
> interfName fn = rootname fn ++ icurryExt

> objectName :: Bool -> FilePath -> FilePath
> objectName debug = name (if debug then debugExt else oExt)
>   where name ext fn = rootname fn ++ ext

> curryExt, lcurryExt, icurryExt, oExt, debugExt :: String
> curryExt = ".curry"
> lcurryExt = ".lcurry"
> icurryExt = ".icurry"
> oExt = ".o"
> debugExt = ".d.o"

> sourceExts, moduleExts :: [String]
> sourceExts = [lcurryExt,curryExt]
> moduleExts = sourceExts ++ [icurryExt]

\end{verbatim}
