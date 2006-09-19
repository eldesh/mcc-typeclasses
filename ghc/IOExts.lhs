% -*- LaTeX -*-
% $Id: IOExts.lhs 1833 2005-11-12 14:39:21Z wlux $
%
% Copyright (c) 2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{hlib/IOExts.lhs}
\subsection{Mutable References for ghc}\label{sec:ghc-ioexts}
The traditional \texttt{IOExts} module is deprecated in ghc version
$6.x$ and may not be present in later versions. In order to preserve
compatibility with older versions, we provide a wrapper around
\texttt{Data.IORef}. Note that this module is also part of the
hierarchical libraries distributed with nhc version $1.16$ and later.
However, the nhc implementation does not define an equality instance
for \texttt{IORef} and therefore we continue using the wrapper
described in Sect.~\ref{sec:nhc-ioexts}.
\begin{verbatim}

> module IOExts(module Data.IORef) where
> import Data.IORef(IORef, newIORef,readIORef,writeIORef)

\end{verbatim}
