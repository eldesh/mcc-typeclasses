% -*- LaTeX -*-
% $Id$
%
% Copyright (c) 2019, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{hs98/Semigroup.lhs}
\section{Semigroup}\label{sec:semigroup}
The \texttt{Semigroup} class captures the notion of a semigroup, which
is a type with a single associative binary operation. This operation
is called \texttt{(<>)} here. The class was introduced in version 8 of
the Glasgow Haskell compiler and is (re)exported from the Prelude as
part of the ``Semigroup (as superclass of) Monoid Proposal'' since
version 8.4.

We provide a trivial version of the class's definition here to be used
with older compilers.
\begin{verbatim}

> module Semigroup where
> infixr 6 <>

> class Semigroup a where
>   (<>) :: a -> a -> a

\end{verbatim}
