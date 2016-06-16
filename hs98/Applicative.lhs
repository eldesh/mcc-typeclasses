% -*- LaTeX -*-
% $Id: Applicative.lhs 3229 2016-06-16 09:08:31Z wlux $
%
% Copyright (c) 2015, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{hs98/Applicative.lhs}
\section{Applicative functors}\label{sec:applicative}
The \texttt{Applicative} class was proposed
in~\cite{McBridePaterson08:Applicative} as an abstraction for an
``applicative style of effectful programming''. Together with the
\texttt{Alternative} class it is going to become part of the Haskell
standard library. For older compilers we provide an implementation
based on the paper here.
\begin{verbatim}

> module Applicative where
> infixl 4 <*>, *>, <*, <$>, <$, <**>
> infixl 3 <|>

> class Functor f => Applicative f where
>   pure :: a -> f a
>   (<*>) :: f (a -> b) -> f a -> f b

> (<$>) :: Functor f => (a -> b) -> f a -> f b
> f <$> x = fmap f x

\end{verbatim}
Below are some useful combinators, which are part of the standard
library implementation.
\begin{verbatim}

> (<$) :: Functor f => a -> f b -> f a
> x <$ a = const x <$> a

> (<**>) :: Applicative f => f a -> f (a -> b) -> f b
> a <**> b = (\x f -> f x) <$> a <*> b

> (*>) :: Applicative f => f a -> f b -> f b
> a *> b = const id <$> a <*> b

> (<*) :: Applicative f => f a -> f b -> f a
> a <* b = const <$> a <*> b

> liftA :: Applicative f => (a -> b) -> f a -> f b
> liftA f a = f <$> a

> liftA2 :: Applicative f => (a -> b -> c) -> f a -> f b -> f c
> liftA2 f a b = f <$> a <*> b

> liftA3 :: Applicative f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
> liftA3 f a b c = f <$> a <*> b <*> c

> sequenceA :: Applicative f => [f a] -> f [a]
> sequenceA = foldr (liftA2 (:)) (pure [])

\end{verbatim}
As shown in the paper, an \texttt{Applicative} instance can be defined
for every type with a \texttt{Monad} instance using the
\texttt{return} and \texttt{ap} functions. Below we define instances
for all Prelude types with a \texttt{Monad} instance. The paper also
defines an instance for the type \texttt{((->) env)}, however we omit
that instance here.
\begin{verbatim}

> instance Applicative [] where
>   pure x = [x]
>   fs <*> xs = [f x | f <- fs, x <- xs]

> instance Applicative IO where
>   pure x = return x
>   m1 <*> m2 = m1 >>= \f -> m2 >>= \x -> return (f x)

> instance Applicative Maybe where
>   pure x = Just x
>   Just f <*> mb = fmap f mb
>   Nothing <*> _ = Nothing

\end{verbatim}
The \texttt{Alternative} class is an extension of the
\texttt{Applicative} class, which was not introduced in the paper but
is defined along with it in the standard library implementation.
\begin{verbatim}

> class Applicative f => Alternative f where
>   empty :: f a
>   (<|>) :: f a -> f a -> f a

> instance Alternative [] where
>   empty = []
>   xs <|> ys = xs ++ ys

> many :: Alternative f => f a -> f [a]
> many x = some x <|> pure []

> some :: Alternative f => f a -> f [a]
> --some x = (:) <$> x <*> many x
> some x = (:) <$> x <*> (some x <|> pure [])

> optional :: Alternative f => f a -> f (Maybe a)
> optional a = liftA Just a <|> liftA (const Nothing) empty

\end{verbatim}
Note that the first definition of \texttt{some} is commented out
because it does not compile under nhc. This is due to a -- known --
bug in the type checker of nhc which expects a default declaration
when compiling mutually recursive functions with class constraints.
However, no such default can be given in the above case because
neither of the types involved is a numeric type.
