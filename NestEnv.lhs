% -*- LaTeX -*-
% $Id: NestEnv.lhs 1848 2006-02-06 09:03:30Z wlux $
%
% Copyright (c) 1999-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{NestEnv.lhs}
\subsection{Nested Environments}
The \texttt{NestEnv} environment type extends top-level environments
(see section~\ref{sec:toplevel-env}) to manage nested scopes. Local
scopes allow only for a single, unambiguous definition.

For convenience, the type \texttt{TopEnv} is exported by the module
\texttt{NestEnv}.
\begin{verbatim}

> module NestEnv(NestEnv, TopEnv, Entity(..),
>                globalBindNestEnv, localBindNestEnv, qualBindNestEnv,
>                lookupNestEnv, qualLookupNestEnv,
>                toplevelEnv, globalEnv, nestEnv) where
> import Env
> import TopEnv
> import Ident

> data NestEnv a = GlobalEnv (TopEnv a) | LocalEnv (NestEnv a) (Env Ident a)
>                  deriving Show

> instance Functor NestEnv where
>   fmap f (GlobalEnv env) = GlobalEnv (fmap f env)
>   fmap f (LocalEnv genv env) = LocalEnv (fmap f genv) (fmap f env)

\end{verbatim}
The functions \texttt{globalBindNestEnv} and \texttt{localBindNestEnv}
implement binding of global and local definitions, respectively. The
former introduces bindings for the qualified and unqualified names of
an entity, the latter only for the unqualified name.
\begin{verbatim}

> globalBindNestEnv :: ModuleIdent -> Ident -> a -> NestEnv a -> NestEnv a
> globalBindNestEnv m x y (GlobalEnv env) =
>   GlobalEnv (globalBindTopEnv m x y env)
> globalBindNestEnv _ _ _ (LocalEnv _ _) =
>   error "internal error: globalBindNestEnv"

> localBindNestEnv :: Ident -> a -> NestEnv a -> NestEnv a
> localBindNestEnv _ _ (GlobalEnv _) =
>   error "internal error: localBindNestEnv"
> localBindNestEnv x y (LocalEnv genv env) =
>   case lookupEnv x env of
>     Just _ -> error "internal error: bindNestEnv"
>     Nothing -> LocalEnv genv (bindEnv x y env)

> qualBindNestEnv :: QualIdent -> a -> NestEnv a -> NestEnv a
> qualBindNestEnv x y (GlobalEnv env) = GlobalEnv (qualBindTopEnv x y env)
> qualBindNestEnv x y (LocalEnv genv env)
>   | isQualified x = error "internal error: qualBindNestEnv"
>   | otherwise =
>       case lookupEnv x' env of
>         Just _ -> error "internal error: qualBindNestEnv"
>         Nothing -> LocalEnv genv (bindEnv x' y env)
>   where x' = unqualify x

> lookupNestEnv :: Ident -> NestEnv a -> [a]
> lookupNestEnv x (GlobalEnv env) = lookupTopEnv x env
> lookupNestEnv x (LocalEnv genv env) =
>   case lookupEnv x env of
>     Just y -> [y]
>     Nothing -> lookupNestEnv x genv

> qualLookupNestEnv :: QualIdent -> NestEnv a -> [a]
> qualLookupNestEnv x env
>   | isQualified x = qualLookupTopEnv x (toplevelEnv env)
>   | otherwise = lookupNestEnv (unqualify x) env

\end{verbatim}
The function \texttt{toplevelEnv} returns the top-level environment of
a nested environment discarding all local scopes. The function
\texttt{globalEnv} transforms a flat top-level environment into a
nested environment and \texttt{nestEnv} opens a new nesting scope.
\begin{verbatim}

> toplevelEnv :: NestEnv a -> TopEnv a
> toplevelEnv (GlobalEnv env) = env
> toplevelEnv (LocalEnv genv _) = toplevelEnv genv

> globalEnv :: TopEnv a -> NestEnv a
> globalEnv = GlobalEnv

> nestEnv :: NestEnv a -> NestEnv a
> nestEnv env = LocalEnv env emptyEnv

\end{verbatim}
