% -*- LaTeX -*-
% $Id:$
%
% Copyright (c) 2015, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Files.lhs}
\section{Source, interface and object files}
\begin{verbatim}

> module Files where
> import Directory
> import IO
> import PathUtils
> import System

\end{verbatim}
The compiler uses two distinct import paths to locate source modules
and their interfaces on one hand and standard library interfaces on
the other hand. The former are specified on the command line with
\texttt{-i} options and the latter with \texttt{-P} options. We take
that the order of arguments on the command line matters and therefore
mix both kinds of paths in a single list.
\begin{verbatim}

> data ImportPath = ImpDir FilePath | LibDir FilePath deriving Show

\end{verbatim}
The default standard library import path is assumed to be set in the
environment variable \texttt{CURRY\_IMPORT\_PATH}, while the default
import path for source modules is empty, meaning that they will be
looked up only relative to the current directory.
\begin{verbatim}

> getCurryImportPath :: IO [ImportPath]
> getCurryImportPath =
>   IO.catch (getEnv "CURRY_IMPORT_PATH" >>= return . map LibDir . pathList)
>            (const (return []))

\end{verbatim}
The function \texttt{filesInPath} computes a list of filenames from an
import path and a relative filename. The function
\texttt{filesInPathWithExts} is similar, but it also uses two lists of
extensions, which are appended to the filename. The first of these
lists is used for the directories in the source import path and the
other is used for the directories in the standard library import path.
\begin{verbatim}

> filesInPath :: [ImportPath] -> FilePath -> [FilePath]
> filesInPath importPath fn = [dir p `catPath` fn | p <- importPath]
>   where dir (ImpDir dir) = dir
>         dir (LibDir dir) = dir

> filesInPathWithExts :: [String] -> [String] -> [ImportPath] -> FilePath
>                     -> [FilePath]
> filesInPathWithExts impExts libExts importPath fn =
>   [dir `catPath` fn ++ e | (dir,es) <- map exts importPath, e <- es]
>   where exts (ImpDir dir) = (dir,impExts)
>         exts (LibDir dir) = (dir,libExts)

\end{verbatim}
The function \texttt{lookupFile} can be used to search for files. It
returns the first name from the argument list for which a regular file
exists in the file system.
\begin{verbatim}

> lookupFile :: [FilePath] -> IO (Maybe FilePath)
> lookupFile [] = return Nothing
> lookupFile (fn:fns) =
>   do
>     so <- doesFileExist fn
>     if so then return (Just fn) else lookupFile fns

\end{verbatim}
The functions \texttt{interfName} and \texttt{objectName} compute the
name of the interface and object file, respectively, corresponding to
a source module. Note that output files are always created in the same
directory as the source file.
\begin{verbatim}

> interfName :: FilePath -> FilePath
> interfName fn = rootname fn ++ icurryExt

> objectName :: Bool -> FilePath -> FilePath
> objectName debug = name (if debug then debugExt else oExt)
>   where name ext fn = rootname fn ++ ext

> curryExt, lcurryExt, icurryExt, cExt, oExt, debugExt :: String
> curryExt = ".curry"
> lcurryExt = ".lcurry"
> icurryExt = ".icurry"
> cExt = ".c"
> oExt = ".o"
> debugExt = ".d.o"

> sourceExts, intfExts, moduleExts :: [String]
> sourceExts = [lcurryExt,curryExt]
> intfExts = [icurryExt]
> moduleExts = sourceExts ++ intfExts

\end{verbatim}
