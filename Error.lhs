% -*- LaTeX -*-
% $Id: Error.lhs 1912 2006-05-03 14:53:33Z wlux $
%
% Copyright (c) 2003-2006, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Error.lhs}
\section{Errors}\label{sec:error}
The \texttt{Error} type is used for describing the result of a
computation that can fail. In contrast to the standard \texttt{Maybe}
type, its \texttt{Error} case provides for a list of error messages
that describes the failure.
\begin{verbatim}

> module Error where
> import List
> import Monad

> infixl 1 &&&, &&>

> data Error a = Ok a | Errors [String] deriving (Eq,Ord,Show)

> instance Functor Error where
>   fmap f (Ok x) = Ok (f x)
>   fmap _ (Errors es) = Errors es

> instance Monad Error where
>   fail s = Errors [s]
>   return x = Ok x
>   Ok x      >>= f = f x
>   Errors es >>= _ = Errors es

> ok :: Error a -> a
> ok (Ok x) = x
> ok (Errors es) = error (concat (intersperse "\n" (nub es)))

> okM :: Monad m => Error a -> m a
> okM (Ok x) = return x
> okM (Errors es) = fail (concat (intersperse "\n" (nub es)))

\end{verbatim}
By using a list of error messages, the \texttt{Error} type is prepared
to report more than one error. However, the standard \texttt{Monad}
instance restricts error reporting to at most one error because the
operator \texttt{(>>=)} cannot pass a value to its second argument
when the first argument detects an error. This is particularly
annoying if there ars sub-expressions in the second argument that do
not depend on the result of the first expression. For instance,
consider the problem of checking an application. Given a data
constructor \texttt{Apply Expression Expression} and a function
\texttt{check :: Expression -> Expression}, the \texttt{Apply} case of
this function will look similar to
\begin{verbatim}
  check (Apply e1 e2) =
    check e1 >>= \e1' ->
    check e2 >>= \e2' ->
    return (Apply e1' e2')
\end{verbatim}
\texttt{Check e2} does not use the value \texttt{e1'} so it should be
possible to report errors from both \texttt{e1} and \texttt{e2}. To
that end, we introduce a new combinator \verb|(&&&)| that executes two
independent (error) monads and then combines their results. With the
new operator, the \texttt{Apply} case of \texttt{check} can now be
implemented as follows
\begin{verbatim}
  check (Apply e1 e2) =
    check e1 &&& check e2 >>= \(e1',e2') ->
    return (Apply e1 e2')
\end{verbatim}
\begin{verbatim}

> (&&&) :: Error a -> Error b -> Error (a,b)
> Ok x       &&& Ok y       = Ok (x,y)
> Ok _       &&& Errors es  = Errors es
> Errors es  &&& Ok _       = Errors es
> Errors es1 &&& Errors es2 = Errors (es1 ++ es2)

\end{verbatim}
The function \verb|(&&>)| is a variant of \verb|(&&&)| that returns
only the result of its second argument.
\begin{verbatim}

> (&&>) :: Error a -> Error b -> Error b
> x &&> y = liftM snd (x &&& y)

\end{verbatim}
For convenience, we introduce variants of some monad functions that
use \verb|(&&&)| and \verb|(&&>)| instead of \texttt{(>>=)} and
\texttt{(>>)}, respectively. The function \texttt{liftE} is equivalent
to \texttt{liftM} and included only for consistency.
\begin{verbatim}

> liftE :: (a -> b) -> Error a -> Error b
> liftE = liftM

> liftE2 :: (a -> b -> c) -> Error a -> Error b -> Error c
> liftE2 f x y = liftE (uncurry f) (x &&& y)

> liftE3 :: (a -> b -> c -> d) -> Error a -> Error b -> Error c -> Error d
> liftE3 f x y z = liftE (uncurry (uncurry f)) (x &&& y &&& z)

> sequenceE :: [Error a] -> Error [a]
> sequenceE = foldr (liftE2 (:)) (return [])

> sequenceE_ :: [Error a] -> Error ()
> sequenceE_ = foldr (&&>) (return ())

> mapE :: (a -> Error b) -> [a] -> Error [b]
> mapE f xs = sequenceE (map f xs)

> mapE_ :: (a -> Error b) -> [a] -> Error ()
> mapE_ f xs = sequenceE_ (map f xs)

> zipWithE :: (a -> b -> Error c) -> [a] -> [b] -> Error [c]
> zipWithE f xs ys = sequenceE (zipWith f xs ys)

> zipWithE_ :: (a -> b -> Error c) -> [a] -> [b] -> Error ()
> zipWithE_ f xs ys = sequenceE_ (zipWith f xs ys)

\end{verbatim}
