% -*- LaTeX -*-
% $Id: Ident.lhs 2690 2008-05-01 20:40:17Z wlux $
%
% Copyright (c) 1999-2008, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Ident.lhs}
\section{Identifiers}
This module provides the implementation of identifiers and some
utility functions for identifiers, which are used at various places in
the compiler.

Identifiers comprise the name of the denoted entity and an \emph{id},
which can be used for renaming identifiers, e.g., in order to resolve
name conflicts between identifiers from different scopes. An
identifier with an \emph{id} $0$ is considered as not being renamed
and, hence, its \emph{id} will not be shown.

\ToDo{Probably we should use \texttt{Integer} for the \emph{id}s.}

Qualified identifiers may optionally be prefixed by a module
name. \textbf{The order of the cases \texttt{UnqualIdent} and
\texttt{QualIdent} is important. Some parts of the compiler rely on
the fact that all qualified identifiers are greater than any
unqualified identifier.}
\begin{verbatim}

> module Ident(Ident,QualIdent,ModuleIdent,
>              mkIdent,name,qualName,uniqueId,
>              renameIdent,unRenameIdent,isRenamed,
>              mkMIdent,moduleName,moduleQualifiers,isInfixOp,isQInfixOp,
>              qualify,qualifyWith,qualifyLike,qualQualify,isQualified,
>              unqualify,qualUnqualify,localIdent,splitQualIdent,
>              anonId) where
> import Char
> import List

> data Ident = Ident String Int deriving (Eq,Ord)
> data QualIdent = UnqualIdent Ident | QualIdent ModuleIdent Ident
>                  deriving (Eq,Ord)
> newtype ModuleIdent = ModuleIdent [String] deriving (Eq,Ord)

> instance Show Ident where
>   showsPrec _ (Ident x n)
>     | n == 0 = showString x
>     | otherwise = showString x . showChar '.' . shows n
> instance Show QualIdent where
>   showsPrec _ (UnqualIdent x) = shows x
>   showsPrec _ (QualIdent m x) = shows m . showChar '.' . shows x
> instance Show ModuleIdent where
>   showsPrec _ m = showString (moduleName m)

> mkIdent :: String -> Ident
> mkIdent x = Ident x 0

> name :: Ident -> String
> name (Ident x _) = x

> qualName :: QualIdent -> String
> qualName (UnqualIdent x) = name x
> qualName (QualIdent m x) = moduleName m ++ "." ++ name x

> uniqueId :: Ident -> Int
> uniqueId (Ident _ n) = n

> renameIdent :: Ident -> Int -> Ident
> renameIdent (Ident x _) n = Ident x n

> unRenameIdent :: Ident -> Ident
> unRenameIdent (Ident x _) = Ident x 0

> isRenamed :: Ident -> Bool
> isRenamed (Ident _ n) = n /= 0

> mkMIdent :: [String] -> ModuleIdent
> mkMIdent = ModuleIdent

> moduleName :: ModuleIdent -> String
> moduleName (ModuleIdent xs) = concat (intersperse "." xs)

> moduleQualifiers :: ModuleIdent -> [String]
> moduleQualifiers (ModuleIdent xs) = xs

> isInfixOp :: Ident -> Bool
> isInfixOp (Ident ('<':c:cs) _) =
>   last (c:cs) /= '>' || not (isAlphaNum c) && c `notElem` "_(["
> isInfixOp (Ident (c:_) _) = not (isAlphaNum c) && c `notElem` "_(["
> isInfixOp (Ident _ _) = False -- error "Zero-length identifier"

> isQInfixOp :: QualIdent -> Bool
> isQInfixOp (UnqualIdent x) = isInfixOp x
> isQInfixOp (QualIdent _ x) = isInfixOp x

\end{verbatim}
The functions \texttt{qualify} and \texttt{qualifyWith} convert an
unqualified identifier into a qualified identifier (without and with a
given module prefix, respectively).
\begin{verbatim}

> qualify :: Ident -> QualIdent
> qualify = UnqualIdent

> qualifyWith :: ModuleIdent -> Ident -> QualIdent
> qualifyWith = QualIdent

> qualifyLike :: QualIdent -> Ident -> QualIdent
> qualifyLike (UnqualIdent _) x = UnqualIdent x
> qualifyLike (QualIdent m _) x = QualIdent m x

> qualQualify :: ModuleIdent -> QualIdent -> QualIdent
> qualQualify m (UnqualIdent x) = QualIdent m x
> qualQualify _ x = x

> isQualified :: QualIdent -> Bool
> isQualified (UnqualIdent _) = False
> isQualified (QualIdent _ _) = True

> unqualify :: QualIdent -> Ident
> unqualify (UnqualIdent x) = x
> unqualify (QualIdent _ x) = x

> qualUnqualify :: ModuleIdent -> QualIdent -> QualIdent
> qualUnqualify m (UnqualIdent x) = UnqualIdent x
> qualUnqualify m (QualIdent m' x)
>   | m == m' = UnqualIdent x
>   | otherwise = QualIdent m' x

> localIdent :: ModuleIdent -> QualIdent -> Maybe Ident
> localIdent _ (UnqualIdent x) = Just x
> localIdent m (QualIdent m' x)
>   | m == m' = Just x
>   | otherwise = Nothing

> splitQualIdent :: QualIdent -> (Maybe ModuleIdent,Ident)
> splitQualIdent (UnqualIdent x) = (Nothing,x)
> splitQualIdent (QualIdent m x) = (Just m,x)

\end{verbatim}
The ubiquitous anonymous identifier is defined here, too.
\begin{verbatim}

> anonId :: Ident
> anonId = Ident "_" 0

\end{verbatim}
