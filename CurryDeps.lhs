% -*- LaTeX -*-
% $Id: CurryDeps.lhs 3220 2016-06-15 22:32:30Z wlux $
%
% Copyright (c) 2002-2015, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CurryDeps.lhs}
\section{Building Programs}\label{sec:dependencies}
This module implements the functions to compute the dependency
information between Curry modules. This is used to create Makefile
dependencies and to update programs composed of multiple modules.
\begin{verbatim}

> module CurryDeps(buildScript, makeDepend, findModules) where
> import Curry hiding(Interface(..))
> import CurryParser
> import Env
> import Error
> import Files
> import IO
> import List
> import Maybe
> import Monad
> import PathUtils
> import PredefIdent
> import SCC
> import Unlit

> data Source = Source FilePath [ModuleIdent]
>             | Interface FilePath
>             | Unknown
>             deriving (Eq,Ord,Show)
> type SourceEnv = Env ModuleIdent Source

\end{verbatim}
The module has three entry points. The function \texttt{buildScript}
computes either a build or a clean script for a module, the function
\texttt{makeDepend} computes dependency rules for inclusion into a
Makefile, and the function \texttt{findModules} tries to find a source
or interface file for each module.
\begin{verbatim}

> buildScript :: Bool -> Bool -> [ImportPath] -> Maybe String
>             -> Maybe FilePath -> FilePath -> IO [String]
> buildScript clean debug paths goal output fn =
>   do
>     (ms,es) <- fmap (flattenDeps . sortDeps) (deps paths emptyEnv fn)
>     when (null es) (putStr (makeScript clean debug goal target ms))
>     return es
>   where target
>           | extension fn `elem` moduleExts ++ [oExt] = Nothing
>           | otherwise = output `mplus` Just fn
>         makeScript clean = if clean then makeCleanScript else makeBuildScript

> makeDepend :: [ImportPath] -> Maybe FilePath -> [FilePath] -> IO ()
> makeDepend paths output ms =
>   foldM (deps paths) emptyEnv ms >>= maybe putStr writeFile output . makeDeps

> deps :: [ImportPath] -> SourceEnv -> FilePath -> IO SourceEnv
> deps paths mEnv fn
>   | e `elem` sourceExts = sourceDeps paths (mkMIdent [r]) mEnv fn
>   | e == icurryExt = return mEnv
>   | e == oExt = targetDeps paths mEnv r
>   | otherwise = targetDeps paths mEnv fn
>   where r = rootname fn
>         e = extension fn

> targetDeps :: [ImportPath] -> SourceEnv -> FilePath -> IO SourceEnv
> targetDeps paths mEnv fn =
>   lookupFile [fn ++ e | e <- sourceExts] >>=
>   maybe (return (bindEnv m Unknown mEnv)) (sourceDeps paths m mEnv)
>   where m = mkMIdent [fn]

> findModules :: [ImportPath] -> Maybe FilePath -> [FilePath] -> IO ()
> findModules paths output ms =
>   mapM (\fn -> liftM ((fn ++ ": ") ++) (findModule paths fn)) ms >>=
>   maybe putStr writeFile output . unlines

> findModule :: [ImportPath] -> FilePath -> IO FilePath
> findModule paths fn
>   | e `elem` sourceExts = return fn
>   | e == icurryExt = lookupModule [] (mkMIdent [r]) >>= return . fromMaybe fn
>   | e == oExt = lookupModule [] (mkMIdent [r]) >>= return . fromMaybe ""
>   | otherwise =
>       lookupModule paths (mkMIdent (components fn)) >>= return . fromMaybe ""
>   where r = rootname fn
>         e = extension fn
>         components fn =
>           case break ('.' ==) fn of
>             (fn',"") -> [fn']
>             (fn',_:fn'') -> fn' : components fn''

\end{verbatim}
The following function is used to look up files related to a given
module. Whereas source files for targets are looked up in the current
directory only, imported modules are looked up also in the search
path. Directories specified with \texttt{-i} options are used for
looking up source and interface files, whereas directories specified
with \texttt{-P} options are used for looking up only interface files.
\begin{verbatim}

> lookupModule :: [ImportPath] -> ModuleIdent -> IO (Maybe FilePath)
> lookupModule paths m =
>   lookupFile (filesInPathWithExts moduleExts intfExts (ImpDir "" : paths) fn)
>   where fn = foldr1 catPath (moduleQualifiers m)

\end{verbatim}
In order to compute the dependency graph, source files for each module
need to be looked up. When a source module is found, its header is
parsed in order to determine the modules that it imports, and
dependencies for these modules are computed recursively. The Prelude
is added implicitly to the list of imported modules except for the
Prelude itself. Any errors reported by the parser are ignored.
\begin{verbatim}

> moduleDeps :: [ImportPath] -> SourceEnv -> ModuleIdent -> IO SourceEnv
> moduleDeps paths mEnv m =
>   case lookupEnv m mEnv of
>     Just _ -> return mEnv
>     Nothing ->
>       do
>         mbFn <- lookupModule paths m
>         case mbFn of
>           Just fn
>             | icurryExt `isSuffixOf` fn ->
>                 return (bindEnv m (Interface fn) mEnv)
>             | otherwise -> sourceDeps paths m mEnv fn
>           Nothing -> return (bindEnv m Unknown mEnv)

> sourceDeps :: [ImportPath] -> ModuleIdent -> SourceEnv -> FilePath
>            -> IO SourceEnv
> sourceDeps paths m mEnv fn =
>   do
>     s <- readFile fn
>     case parseHeader fn (unlitLiterate fn s) of
>       Ok (Module m' _ is _) ->
>         let ms = imports m' is in
>         foldM (moduleDeps paths) (bindEnv m (Source fn ms) mEnv) ms
>       Errors _ -> return (bindEnv m (Source fn []) mEnv)

> imports :: ModuleIdent -> [ImportDecl] -> [ModuleIdent]
> imports m ds = nub $
>   [preludeMIdent | m /= preludeMIdent] ++ [m | ImportDecl _ m _ _ _ <- ds]

> unlitLiterate :: FilePath -> String -> String
> unlitLiterate fn
>   | lcurryExt `isSuffixOf` fn = snd . unlit fn
>   | otherwise = id

\end{verbatim}
It is quite straightforward to generate Makefile dependencies from
the dependency environment. In order for these dependencies to work,
the Makefile must include a rule
\begin{verbatim}
.SUFFIXES: .lcurry .curry .icurry
.o.icurry: @echo interface $@ not found, remove $< and recompile; exit 1
\end{verbatim}
This dependency rule introduces an indirect dependency between a
module and its interface. In particular, the interface may be updated
when the module is recompiled and a new object file is generated but
it does not matter if the interface is out of date with respect to the
object code.
\begin{verbatim}

> makeDeps :: SourceEnv -> String
> makeDeps mEnv =
>   unlines [depsLine fn ms | Source fn ms <- map snd (envToList mEnv)]
>   where depsLine fn ms =
>           objectName False fn ++ ": " ++ fn ++ " " ++
>           unwords (filter (not . null) (map interf ms))
>         interf m = maybe [] interfFile (lookupEnv m mEnv)
>         interfFile (Source fn _) = interfName fn
>         interfFile (Interface fn) = fn
>         interfFile Unknown = ""

\end{verbatim}
If we want to compile the program instead of generating Makefile
dependencies, the environment has to be sorted topologically. Note
that the dependency graph must not contain any cycles, i.e., we cannot
handle modules which are mutually recursive at present.

\ToDo{Accept cyclic import dependencies between modules, but require
  that enough boot (source or interface) files are present in order to
  break each cycle.}
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
generated script uses commands of the form
\begin{quote}
  \texttt{compile} $i$ $n$ \emph{source} \emph{interface}
  \emph{object} \emph{interface$_1$} \dots{} \emph{interface$_k$}
\end{quote}
and
\begin{quote}
  \texttt{link} $i$ $n$ \emph{target} \emph{module-list}
  \emph{object$_1$} \dots{} \emph{object$_l$}
\end{quote}
where \emph{source} is a source file, \emph{interface} and
\emph{object} are the interface and object files to be generated,
\emph{interface$_1$}, \dots, \emph{interface$_k$} are the interface
files on which \emph{source} depends, \emph{target} is the executable,
and \emph{object$_1$}, \dots, \emph{object$_l$} are the object files
to be linked. The \emph{module-list} is equal to
\texttt{-M}\emph{module$_m$} if no explicit goal has been specified on
the commmand line and equal to \texttt{-M}\emph{module$_1$} \dots{}
\texttt{-M}\emph{module$_m$} otherwise, where \emph{module$_1$},
\dots, \emph{module$_m$} are the modules of the program and
\emph{module$_m$} in particular is the main module of the program. The
numbers $i$ and $n$ give the index of the current command and the
total number of commands in the build script, respectively. These
numbers can be used to provide feedback to the user about the progress
of building the target. Note that the index of the first command is 1,
not 0. The number $i$ actually is redundant for a \texttt{link}
command since it will always be the last command of a build script. Of
course, the commands \verb|compile| and \verb|link| must be defined in
the environment where the script is executed.

\ToDo{Provide support for an equivalent of \texttt{make -k}.}
\begin{verbatim}

> makeBuildScript :: Bool -> Maybe String -> Maybe FilePath
>                 -> [(ModuleIdent,Source)] -> String
> makeBuildScript debug goal target mEnv = unlines cmds
>   where n = length cmds
>         sources = [(fn,ms) | (_,Source fn ms) <- mEnv]
>         cmds = zipWith compile [1..] sources ++ map link (maybeToList target)
>         compile i (fn,ms) =
>           command ("compile" : show i : show n : fn : ifn : ofn : ifns)
>           where ifn = interfName fn
>                 ofn = objectName debug fn
>                 ifns = catMaybes (map interf ms)
>         link fn = command ("link" : show n : show n : fn : ms ++ os)
>           where m0 = last mEnv
>                 ms = catMaybes (map modul (maybe [m0] (const mEnv) goal))
>                 os = reverse (map (objectName debug . fst) sources)
>         modul (_,Source fn _) = Just ("-M" ++ fn)
>         modul (m,Interface _) = Just ("-M" ++ moduleName m)
>         modul (_,Unknown) = Nothing
>         interf m =
>           case lookup m mEnv of
>             Just (Source fn _) -> Just (interfName fn)
>             Just (Interface fn) -> Just fn
>             Just Unknown -> Nothing
>             Nothing -> Nothing

> command :: [String] -> String
> command = unwords . map quote

> quote :: String -> String
> quote cs = "'" ++ foldr quoteChar "'" cs
>   where quoteChar c cs = if c == '\'' then "'\\''" ++ cs else c:cs

\end{verbatim}
The function \texttt{makeCleanScript} returns a shell script that
removes all compiled files for a module. The generated script consists
of commands of the form
\begin{quote}
  \texttt{remove} \emph{file$_1$} \dots{} \emph{file$_n$}
\end{quote}
where the \verb|remove| command must be defined in the environment
where the script is executed.
\begin{verbatim}

> makeCleanScript :: Bool -> Maybe String -> Maybe FilePath
>                 -> [(ModuleIdent,Source)] -> String
> makeCleanScript debug _ target mEnv =
>   command ("remove" : foldr (files . snd) (maybeToList target) mEnv)
>   where d = if debug then 2 else 0
>         files (Source fn _) fs =
>           drop d [interfName fn,objectName False fn,objectName True fn] ++ fs
>         files (Interface _) fs = fs
>         files Unknown fs = fs

\end{verbatim}
