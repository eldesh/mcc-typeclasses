% -*- LaTeX -*-
% $Id: Utils.lhs 3225 2016-06-16 08:40:29Z wlux $
%
% Copyright (c) 2001-2015, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Utils.lhs}
\section{Utility Functions}
The module \texttt{Utils} provides a few simple functions that are
commonly used in the compiler, but not implemented in the Haskell
\texttt{Prelude} or standard library.
\begin{verbatim}

> module Utils where
> import Applicative
> import IO
> infixr 5 ++!

\end{verbatim}
\paragraph{Pairs}
The functions \texttt{apFst} and \texttt{apSnd} apply a function to
the first and second components of a pair, resp.
\begin{verbatim}

> apFst f (x,y) = (f x,y)
> apSnd f (x,y) = (x,f y)

\end{verbatim}
\paragraph{Triples}
The \texttt{Prelude} does not contain standard functions for
triples. We provide projection, (un-)currying, and mapping for triples
here.
\begin{verbatim}

> fst3 (x,_,_) = x
> snd3 (_,y,_) = y
> thd3 (_,_,z) = z

> apFst3 f (x,y,z) = (f x,y,z)
> apSnd3 f (x,y,z) = (x,f y,z)
> apThd3 f (x,y,z) = (x,y,f z)

> curry3 f x y z = f (x,y,z)
> uncurry3 f (x,y,z) = f x y z

\end{verbatim}
\paragraph{Strings}
The function \texttt{showLn} is a variant of \texttt{show} that adds a
newline character to the converted string.
\begin{verbatim}

> showLn :: Show a => a -> String
> showLn x = shows x "\n"

\end{verbatim}
\paragraph{Lists}
The function \texttt{(++!)} is variant of the list concatenation
operator \texttt{(++)} that ignores the second argument if the first
is a non-empty list. When lists are used to encode non-determinism in
Haskell, this operator has the same effect as the cut operator in
Prolog, hence the \texttt{!} in the name.
\begin{verbatim}

> (++!) :: [a] -> [a] -> [a]
> xs ++! ys = if null xs then ys else xs

\end{verbatim}
\paragraph{Strict fold}
The function \texttt{foldl\_strict} is a strict version of
\texttt{foldl}, i.e., it evaluates the binary applications before
the recursion. This has the advantage that \texttt{foldl\_strict} does
not construct a large application which is then evaluated in the base
case of the recursion.
\begin{verbatim}

> foldl_strict :: (a -> b -> a) -> a -> [b] -> a
> foldl_strict f z []     = z
> foldl_strict f z (x:xs) = let z' = f z x in  z' `seq` foldl_strict f z' xs

\end{verbatim}
\paragraph{Folding with two lists}
Fold operations with two arguments lists can be defined using
\texttt{zip} and \texttt{foldl} or \texttt{foldr}, resp. Our
definitions are unfolded for efficiency reasons.
\begin{verbatim}

> foldl2 :: (a -> b -> c -> a) -> a -> [b] -> [c] -> a
> foldl2 f z []     _      = z
> foldl2 f z _      []     = z
> foldl2 f z (x:xs) (y:ys) = foldl2 f (f z x y) xs ys

> foldr2 :: (a -> b -> c -> c) -> c -> [a] -> [b] -> c
> foldr2 f z []     _      = z
> foldr2 f z _      []     = z
> foldr2 f z (x:xs) (y:ys) = f x y (foldr2 f z xs ys)

\end{verbatim}
\paragraph{Monadic fold with an accumulator}
The function \texttt{mapAccumM} is a generalization of
\texttt{mapAccumL} to monads like \texttt{foldM} is for
\texttt{foldl}.
\begin{verbatim}

> mapAccumM :: Monad m => (a -> b -> m (a,c)) -> a -> [b] -> m (a,[c])
> mapAccumM _ s [] = return (s,[])
> mapAccumM f s (x:xs) =
>   do
>     (s',y) <- f s x
>     (s'',ys) <- mapAccumM f s' xs
>     return (s'',y:ys)

\end{verbatim}
\paragraph{Applicative variants of mapM and related functions}
We also introduce \texttt{Applicative} variants of the standard
\texttt{sequence}, \texttt{mapM}, and \texttt{zipWithM} functions.
\begin{verbatim}

> sequenceA :: Applicative f => [f a] -> f [a]
> sequenceA = foldr (liftA2 (:)) (pure [])

> sequenceA_ :: Applicative f => [f a] -> f ()
> sequenceA_ = foldr (*>) (pure ())

> mapA :: Applicative f => (a -> f b) -> [a] -> f [b]
> mapA f xs = sequenceA (map f xs)

> mapA_ :: Applicative f => (a -> f b) -> [a] -> f ()
> mapA_ f xs = sequenceA_ (map f xs)

> zipWithA :: Applicative f => (a -> b -> f c) -> [a] -> [b] -> f [c]
> zipWithA f xs ys = sequenceA (zipWith f xs ys)

> zipWithA_ :: Applicative f => (a -> b -> f c) -> [a] -> [b] -> f ()
> zipWithA_ f xs ys = sequenceA_ (zipWith f xs ys)

\end{verbatim}
\paragraph{IO functions}
\begin{verbatim}
The IO actions \texttt{putErr} and \texttt{putErrLn} are variants of
\texttt{putStr} and \texttt{putStrLn} that write their argument string
to the standard error output. Unfortunately, hbc's \texttt{IO} module
lacks a definition of \texttt{hPutStrLn}.
\begin{verbatim}

> putErr :: String -> IO ()
> putErr = hPutStr stderr

> putErrLn :: String -> IO ()
> putErrLn s = putErr (unlines [s])

\end{verbatim}
