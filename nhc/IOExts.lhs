% -*- LaTeX -*-
% $Id: IOExts.lhs 1744 2005-08-23 16:17:12Z wlux $
%
% Copyright (c) 1999-2003, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{nhc/IOExts.lhs}
\subsection{Mutable references for nhc}\label{sec:nhc-ioexts}
Old versions of the nhc compiler implemented mutable references as a
special case of binary I/O using the corresponding library which made
mutable references incompatible with other Haskell
implementations. Since version 1.0, nhc98 supports the same interface as
Hugs and ghc. However, the implementation of \texttt{newIORef} and
\texttt{writeIORef} is too strict in some early releases. The value
stored in the reference is always evaluated to head normal form. As a
work around for this bug, we enclose the arguments in a data type.

\textbf{Don't use a \texttt{newtype} here, because
then $\texttt{Wrap}\,\bot = \bot$!}
\begin{verbatim}

> module IOExts(IORef, newIORef,readIORef,writeIORef) where
#if __NHC__ >= 116
> import qualified NHC.IOExtras as IOExtras
#else
> import qualified IOExtras
#endif

> type IORef a = IOExtras.IORef (Wrap a)
> data Wrap a = Wrap{ unwrap :: a }

> instance Eq IOExtras.IORef where
>   r1 == r2 = IOExtras.unsafePtrEq r1 r2

> newIORef = IOExtras.newIORef . Wrap
> readIORef ior = fmap unwrap (IOExtras.readIORef ior)
> writeIORef ior = IOExtras.writeIORef ior . Wrap

\end{verbatim}
