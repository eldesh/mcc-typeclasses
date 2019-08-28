% -*- LaTeX -*-
% $Id$
%
% Copyright (c) 2019, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{hs2010/Semigroup.lhs}
For ghc, we rely on the preprocessor to either pick the definition
from the \texttt{Data.Semigroup} module or our trivial compatibility
definition.
\begin{verbatim}

> {-# OPTIONS_GHC -cpp #-}
> module Semigroup(Semigroup(..)) where
> #if __GLASGOW_HASKELL__ >= 800
> import Data.Semigroup(Semigroup(..))
> #else
> infixr 6 <>
> class Semigroup a where
>   (<>) :: a -> a -> a
> #endif

\end{verbatim}
