% -*- LaTeX -*-
% $Id: PathUtils.lhs 3220 2016-06-15 22:32:30Z wlux $
%
% Copyright (c) 1999-2015, Wolfgang Lux
% See ../LICENSE for the full license.
%
\nwfilename{unix/PathUtils.lhs}
\section{Path Names}
The module \texttt{PathUtils} implements some utility functions for
manipulating path names and finding files. Depending on the Haskell
compiler and target system, one of the following implementations is
chosen.

\subsection{Unix}
The following implementation of \texttt{PathUtils} uses Unix style
path semantics.
\begin{verbatim}

> module PathUtils(pathSep,curDirPath, isRelative,isAbsolute,
>                  dirname,basename, rootname,extension, catPath,
>                  listSep, pathList) where

\end{verbatim}
With Unix style path semantics, components of a path name are
separated by forward slash characters (\texttt{/}) and file extensions
are separated with a dot character (\texttt{.}).
\begin{verbatim}

> pathSep :: Char
> pathSep = '/'

> curDirPath :: FilePath
> curDirPath = "."

\end{verbatim}
Absolute path names start with a path separator while relative paths
don't.
\begin{verbatim}

> isRelative,isAbsolute :: FilePath -> Bool
> isRelative = not . isAbsolute
> isAbsolute "" = False
> isAbsolute (c:cs) = c == pathSep

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
When we split a path into its directory and base names, we make
sure that the base name does not contain any path separators.
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
The extension of a file name is the component starting at the last dot
of the file name. Note that only an extension in the base name will be
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
Conventionally the colon is used on Unix systems to separate
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
The function \texttt{breakLast} is similar to the standard
\texttt{break} function, except that it splits its argument list at
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
