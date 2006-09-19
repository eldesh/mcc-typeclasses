% -*- LaTeX -*-
% $Id: Position.lhs 1783 2005-10-06 20:35:55Z wlux $
%
% Copyright (c) 2000-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Position.lhs}
\section{Positions}
A source file position consists of a filename, a line number, and a
column number. A tab stop is assumed at every eighth column.
\begin{verbatim}

> module Position where

> data Position =
>   Position{ file :: FilePath, line :: Int, column :: Int }
>   deriving (Eq, Ord)

> instance Show Position where
>   showsPrec _ (Position fn l c) =
>     (if null fn then id else shows fn . showString ", ") .
>     showString "line " . shows l .
>     (if c > 0 then showChar '.' . shows c else id)

> tabWidth :: Int
> tabWidth = 8

> first :: FilePath -> Position
> first fn = Position fn 1 1

> incr :: Position -> Int -> Position
> incr (Position fn l c) n = Position fn l (c + n)

> next :: Position -> Position
> next = flip incr 1

> tab :: Position -> Position
> tab (Position fn l c) = Position fn l (c + tabWidth - (c - 1) `mod` tabWidth)

> nl :: Position -> Position
> nl (Position fn l c) = Position fn (l + 1) 1

\end{verbatim}
The function \texttt{atP} is used for adding position information to
error messages.
\begin{verbatim}

> atP :: Position -> String -> String
> atP p x = show p ++ ": " ++ x

\end{verbatim}
It is sometimes useful to add position information to values of a type
without affecting the type's equality and ordering instances. This is
handled by type \texttt{P} and its \texttt{Eq} and \texttt{Ord}
instances.
\begin{verbatim}

> data P a = P Position a deriving Show

> instance Eq a => Eq (P a) where
>   P _ x == P _ y = x == y
> instance Ord a => Ord (P a) where
>   P _ x `compare` P _ y = x `compare` y

> instance Functor P where
>   fmap f (P p x) = P p (f x)

\end{verbatim}
