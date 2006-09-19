% -*- LaTeX -*-
% $Id: Env.lhs 1744 2005-08-23 16:17:12Z wlux $
%
% Copyright (c) 2002, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Env.lhs}
\section{Environments}
The module \texttt{Env} implements environments. An environment
$\rho = \left\{x_1\mapsto t_1,\dots,x_n\mapsto t_n\right\}$ is a
finite mapping from (finitely many) variables $x_1,\dots,x_n$ to
some kind of expression or term. For any environment we have the
following definitions:
\begin{displaymath}
  \begin{array}{l}
    \rho(x) = \left\{\begin{array}{ll}
        t_i&\mbox{if $x=x_i$}\\
        \bot&\mbox{otherwise}\end{array}\right. \\
    \mathop{{\mathcal D}om}(\rho) = \left\{x_1,\dots,x_n\right\} \\
    \mathop{{\mathcal C}odom}(\rho) = \left\{t_1,\dots,t_n\right\}
  \end{array}
\end{displaymath}

Unfortunately we cannot define \texttt{Env} as a \texttt{newtype}
because of a bug in the nhc compiler.
\begin{verbatim}

> module Env where
> import Map

> newtype Env a b = Env (FM a b) deriving Show

> emptyEnv :: Ord a => Env a b
> emptyEnv = Env zeroFM

> environment :: Ord a => [(a,b)] -> Env a b
> environment = foldr (uncurry bindEnv) emptyEnv

> envToList :: Ord v => Env v e -> [(v,e)]
> envToList (Env rho) = toListFM rho

> bindEnv :: Ord v => v -> e -> Env v e -> Env v e
> bindEnv v e (Env rho) = Env (addToFM v e rho)

> unbindEnv :: Ord v => v -> Env v e -> Env v e
> unbindEnv v (Env rho) = Env (deleteFromFM v rho)

> lookupEnv :: Ord v => v -> Env v e -> Maybe e
> lookupEnv v (Env rho) = lookupFM v rho

> envSize :: Ord v => Env v e -> Int
> envSize (Env rho) = length (toListFM rho)

> instance Ord a => Functor (Env a) where
>   fmap f (Env rho) = Env (fmap f rho)

\end{verbatim}
