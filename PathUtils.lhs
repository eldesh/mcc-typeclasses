% -*- LaTeX -*-
% $Id: PathUtils.lhs 1744 2005-08-23 16:17:12Z wlux $
%
% Copyright (c) 1999-2003, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{PathUtils.lhs}
\section{Pathnames}
This module implements some utility functions for manipulating path
names and finding files.
\begin{verbatim}

> module PathUtils(pathSep,curDirPath, isRelative,isAbsolute,
>                  dirname,basename, rootname,extension, catPath,
>                  listSep, pathList, lookupFile) where
> -- import List
> import Directory

\end{verbatim}
Within this module we assume Unix style path semantics, i.e.\ 
components of a path name are separated by forward slash characters
(\texttt{/}) and file extensions are separated with a dot character
(\texttt{.}).
\begin{verbatim}

> pathSep :: Char
> pathSep = '/'

> curDirPath :: FilePath
> curDirPath = "."

\end{verbatim}
Absolute path names start with a slash while relative paths don't.
\begin{verbatim}

> isRelative,isAbsolute :: FilePath -> Bool
> isRelative = not . isAbsolute
> isAbsolute "" = False
> isAbsolute (c:cs) = c == '/'

\end{verbatim}
Path concatenation on Unix systems is trivial as an empty path also
denotes the current directory. Therefore \texttt{a///b},
\texttt{a/././b}, and \texttt{a/b} all denote the same path.
Nevertheless, we try to avoid inserting redundant slashes here in
order to increase portability.

Note that \texttt{catPath} \emph{dir} \emph{file} ignores \emph{dir}
when \emph{file} is an absolute path.
\begin{verbatim}

> catPath :: FilePath -> FilePath -> FilePath
> catPath dir file
>   | isAbsolute file = file
>   | null dir = file
>   | otherwise = dir ++ if last dir == pathSep then file else pathSep:file

\end{verbatim}
The function \texttt{canonPath} removes redundant path separators from
a file path. In particular, this will remove trailing path separators
from a file path. This behavior is compatible with the standard Unix
tools \texttt{dirname} and \texttt{basename}.

\ToDo{Remove redundant occurrences of \texttt{.} and \texttt{..} in
the path.}

\ToDo{Provide a more general function which performs \texttt{\~}
expansion. Note that such a function will have type \texttt{FilePath
-> IO FilePath}. Also note that the expansion of \texttt{\~}\emph{user}
cannot be implemented portably in Haskell 98.}
\begin{verbatim}

> canonPath :: FilePath -> FilePath
> canonPath "" = ""
> canonPath (c:cs) =
>   c : if c == pathSep then canon (dropWhile (pathSep ==) cs) else canon cs
>   where canon "" = ""
>         canon (c:cs)
>           | c == pathSep = if null cs' then "" else c : canon cs'
>           | otherwise = c : canon cs
>           where cs' = dropWhile (pathSep ==) cs

\end{verbatim}
When we split a path into its basename and directory we will make
sure that the basename does not contain any path separators.
\begin{verbatim}
 
> dirname, basename :: FilePath -> FilePath
> dirname = fst . splitPath . canonPath
> basename = snd . splitPath . canonPath

> splitPath :: FilePath -> (FilePath,FilePath)
> splitPath path =
>   case breakLast (pathSep ==) path of
>     (dirname,"") -> (".",path)
>     (dirname,_:basename) ->
>       (if null dirname then [pathSep] else dirname,basename)

\end{verbatim}
The extension of a filename is the component starting at the last dot
of the filename. Note that only an extension in the basename will be
considered. Also note that the extension will always start with a dot.
\begin{verbatim}

> rootname, extension :: FilePath -> FilePath
> rootname = fst . splitExt . canonPath
> extension = snd . splitExt . canonPath

> splitExt :: FilePath -> (FilePath,String)
> splitExt path =
>   case breakLast ('.' ==) path of
>     (rootname,extension)
>       | pathSep `elem` extension -> (path,"")
>       | otherwise -> (rootname,extension)

\end{verbatim}
Conventionally the colon is used on Unix system to separate
directories in a list of path specifications. The function
\texttt{pathList} converts a single string containing these separators
into a list of strings.
\begin{verbatim}

> listSep :: Char
> listSep = ':'

> pathList :: String -> [String]
> pathList s =
>   case break (listSep ==) s of
>     (s',"") -> [s']
>     (s',_:s'') -> s' : pathList s''

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
The function \texttt{breakLast} is similar to the standard
\texttt{break} function, except that it splits the argument list at
the last position for which the predicate returns \texttt{True}.
\begin{verbatim}

> breakLast :: (a -> Bool) -> [a] -> ([a],[a])
> breakLast p xs =
>   case break p xs of
>     (prefix,[]) -> (prefix,[])
>     (prefix,x:suffix)
>       | null suffix' -> (prefix,x:suffix)
>       | otherwise -> (prefix ++ x:prefix',suffix')
>       where (prefix',suffix') = breakLast p suffix

\end{verbatim}
