% -*- LaTeX -*-
% $Id: IOExts.lhs 1744 2005-08-23 16:17:12Z wlux $
%
% Copyright (c) 1998-2003, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{hbc/IOExts.lhs}
\section{Compatibility modules}
\subsection{Mutable references for hbc}\label{sec:hbc-ioexts}
The Chalmers Haskell compiler implements mutable references in
module \texttt{IOMutVar}. In order to implement an interface which is
compatible with Hugs and Glasgow Haskell, we introduce a wrapper around
the type \texttt{MutableVar} using a \texttt{newtype} so that we can
define an equality instance on this type.\footnote{In principle it
were possible to declare an instance for the type \texttt{MutableVar},
but this instance is not exported by hbc unless the type is exported
itself or the compiler switch \texttt{-fno-inst-with-c-t} is
used. Using the latter is not advisable because the compiler will then
create huge interface files and require up to two times as much memory
in order to compile the Curry compiler.}
\begin{verbatim}

> module IOExts where
> import IOMutVar

> newtype IORef a = IORef (MutableVar a)

> instance Eq (IORef a) where
>   IORef r1 == IORef r2 = r1 `sameVar` r2

> newIORef = fmap IORef . newVar
> readIORef (IORef r) = readVar r
> writeIORef (IORef r) = writeVar r

\end{verbatim}
