% -*- LaTeX -*-
% $Id: PathUtils.lhs 2371 2007-06-23 14:08:14Z wlux $
%
% Copyright (c) 1999-2007, Wolfgang Lux
% See ../LICENSE for the full license.
%
\nwfilename{windows/PathUtils.lhs}
\subsection{Windows}
This implementation of \texttt{PathUtils} uses Windows style path
semantics.
\begin{verbatim}

> module PathUtils(pathSep,curDirPath, isRelative,isAbsolute,
>                  dirname,basename, rootname,extension, catPath,
>                  listSep, pathList, lookupFile) where
> import Directory

\end{verbatim}
We assume that on Windows systems components of a path name are
separated by forward and backward slash characters (\texttt{/} and
\texttt{\char`\\}) and file extensions are separated with a dot
character (\texttt{.}).
\begin{verbatim}

> pathSep :: Char
> pathSep = head pathSeps

> pathSeps :: [Char]
> pathSeps = "/\\"

> curDirPath :: FilePath
> curDirPath = "."

\end{verbatim}
Absolute path names start with a path separator or with a drive letter
followed by a colon.
\begin{verbatim}

> isRelative,isAbsolute :: FilePath -> Bool
> isRelative = not . isAbsolute
> isAbsolute "" = False
> isAbsolute (c:cs) = c `elem` pathSeps || not (null cs) && head cs == ':'

\end{verbatim}
When concatenating paths on Windows systems, we try to avoid inserting
redundant path separators. In particular we must not insert a path
separator after the first path if it simply consists of a drive
letter followed by a colon.

Note that \texttt{catPath} \emph{dir} \emph{file} ignores \emph{dir}
when \emph{file} is an absolute path.
\begin{verbatim}

> catPath :: FilePath -> FilePath -> FilePath
> catPath dir file
>   | isAbsolute file || null dir = file
>   | otherwise = dir ++ if hasTrailingSep dir then file else pathSep:file
>   where hasTrailingSep path = isDrive path || last path `elem` pathSeps
>         isDrive path = length path == 2 && path !! 1 == ':'

\end{verbatim}
The function \texttt{canonPath} removes redundant path separators from
a file path. In particular, this will remove trailing path separators
from a file path. This behavior is compatible with the standard Unix
tools \texttt{dirname} and \texttt{basename}.

\ToDo{Remove redundant occurrences of \texttt{.} and \texttt{..} in
the path.}
\begin{verbatim}

> canonPath :: FilePath -> FilePath
> canonPath "" = ""
> canonPath (c:cs) =
>   case cs of
>     ':':[] -> [c,':']
>     ':':c':cs' -> c : ':' : c' : canon' c' cs'
>     _ -> c : canon' c cs
>   where canon "" = ""
>         canon (c:cs)
>           | c `elem` pathSeps = if null cs' then "" else c : canon cs'
>           | otherwise = c : canon cs
>           where cs' = stripLeadingSeps cs
>         canon' c cs
>           | c `elem` pathSeps = canon (stripLeadingSeps cs)
>           | otherwise = canon cs
>         stripLeadingSeps cs = dropWhile (`elem` pathSeps) cs

\end{verbatim}
When we split a path into its directory and base names, we will make
sure that the base name does not contain a drive letter and no path
separators.
\begin{verbatim}
 
> dirname, basename :: FilePath -> FilePath
> dirname = fst . splitPath . canonPath
> basename = snd . splitPath . canonPath

> splitPath :: FilePath -> (FilePath,FilePath)
> splitPath path =
>   case path of
>     c:':':path' ->
>       case breakLast (`elem` pathSeps) path' of
>         (dirname,"") -> ([c,':'],path')
>         (dirname,_:basename) ->
>           (c : ':' : if null dirname then [pathSep] else dirname,basename)
>     _ ->
>       case breakLast (`elem` pathSeps) path of
>         (dirname,"") -> (".",path)
>         (dirname,_:basename) ->
>           (if null dirname then [pathSep] else dirname,basename)

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
>       | any (`elem` pathSeps) extension -> (path,"")
>       | otherwise -> (rootname,extension)

\end{verbatim}
Conventionally the semicolon is used on Windows system to separate
directories in a list of path specifications. The function
\texttt{pathList} converts a single string containing these separators
into a list of strings.
\begin{verbatim}

> listSep :: Char
> listSep = ';'

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
