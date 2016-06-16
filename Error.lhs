% -*- LaTeX -*-
% $Id: Error.lhs 3225 2016-06-16 08:40:29Z wlux $
%
% Copyright (c) 2003-2015, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Error.lhs}
\section{Errors}\label{sec:error}
The \texttt{Error} type is used for describing the result of a
computation that can fail. In contrast to the standard \texttt{Maybe}
type, its \texttt{Error} case provides for a list of error messages
that describe the failure.

By using a list of error messages, the \texttt{Error} type is prepared
to report more than one error. This is used in the
\texttt{Applicative} instance, where the operator \texttt{(<*>)}
collects the error messages from both arguments. On the other hand,
the standard \texttt{Monad} instance lacks this symmetry because the
operator \texttt{(>>=)} cannot pass a value to its second argument
when the first argument returns an error. For instance, consider an
\texttt{Expression} type with a data constructor
\texttt{Apply Expression Expression} and a function
\verb|check :: Expression -> Error Expression|. If the \texttt{Apply}
case of this function looks similar to
\begin{verbatim}
  check (Apply e1 e2) =
    check e1 >>= \e1' -> check e2 >>= \e2' -> return (Apply e1' e2')
\end{verbatim}
it will not report any errors for the second argument if an error is
detected in the first argument. On the other hand, if the
\texttt{Apply} case looks similar to
\begin{verbatim}
  check (Apply e1 e2) = pure Apply <*> check e1 <*> check e2
\end{verbatim}
the function will report errors for both arguments even if an error is
detected in the first argument.
\begin{verbatim}

> module Error where
> import Applicative
> import List
> import Monad

> data Error a = Ok a | Errors [String] deriving (Eq,Ord,Show)

> instance Functor Error where
>   fmap f (Ok x) = Ok (f x)
>   fmap _ (Errors es) = Errors es

> instance Applicative Error where
>   pure x = Ok x
>   Ok f <*> Ok x = Ok (f x)
>   Ok _ <*> Errors es = Errors es
>   Errors es <*> Ok _ = Errors es
>   Errors es1 <*> Errors es2 = Errors (es1 ++ es2)

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
