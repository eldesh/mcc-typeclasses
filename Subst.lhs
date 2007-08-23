% -*- LaTeX -*-
% $Id: Subst.lhs 2454 2007-08-23 23:06:53Z wlux $
%
% Copyright (c) 2002-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Subst.lhs}
\section{Substitutions}
The module {\tt Subst} implements substitutions. A substitution
$\sigma = \left\{x_1\mapsto t_1,\dots,x_n\mapsto t_n\right\}$ is a
finite mapping from (finitely many) variables $x_1,\dots,x_n$ to
some kind of expression or term.

In order to implement substitutions efficiently composed
substitutions are marked with a boolean flag (see below).
\begin{verbatim}

> module Subst(Subst, idSubst, bindSubst, unbindSubst, compose, substToList,
>              substVar', IntSubst(..), isubstVar, restrictSubstTo) where
> import Map
> import Utils

> data Subst a b = Subst Bool (FM a b) deriving Show

> idSubst :: Ord a => Subst a b
> idSubst = Subst False zeroFM

> substToList :: Ord v => Subst v e -> [(v,e)]
> substToList (Subst _ sigma) = toListFM sigma

> bindSubst :: Ord v => v -> e -> Subst v e -> Subst v e
> bindSubst v e (Subst comp sigma) = Subst comp (addToFM v e sigma)

> unbindSubst :: Ord v => v -> Subst v e -> Subst v e
> unbindSubst v (Subst comp sigma) = Subst comp (deleteFromFM v sigma)

\end{verbatim}
For any substitution we have the following definitions:
\begin{displaymath}
  \begin{array}{l}
    \sigma(x) = \left\{\begin{array}{ll}
        t_i&\mbox{if $x=x_i$}\\
        x&\mbox{otherwise}\end{array}\right. \\
    \mathop{{\mathcal D}om}(\sigma) = \left\{x_1,\dots,x_n\right\} \\
    \mathop{{\mathcal C}odom}(\sigma) = \left\{t_1,\dots,t_n\right\}
  \end{array}  
\end{displaymath}
Note that obviously the set of variables must be a subset of the set
of expressions. Also it is usually possible to extend the substitution
to a homomorphism on the codomain of the substitution. This is
captured by the following class declaration:
\begin{verbatim}

class Ord v => Subst v e where
  var :: v -> e
  subst :: Subst v e -> e -> e

\end{verbatim}
With the help of the injection \texttt{var}, we can then compute the
substitution for a variable $\sigma(v)$ and also the composition of
two substitutions
$(\sigma_1 \circ \sigma_2)(e) \mathop{:=} \sigma_1(\sigma_2(e))$. A
naive implementation of the composition were
\begin{verbatim}
  compose sigma sigma' =
    foldr (uncurry bindSubst) sigma (substToList (fmap (subst sigma) sigma'))
\end{verbatim}
However, such an implementation is very inefficient because the
number of substiutions applied to a variable increases in
$\mathcal{O}(n)$ of the number of compositions.

A more efficient implementation is to apply \texttt{subst} again to
the value substituted for a variable in
$\mathop{{\mathcal D}om}(\sigma)$. However, this is correct only as
long as the result of the substitution does not include any variables
which are in $\mathop{{\mathcal D}om}(\sigma)$. For instance, it is
impossible to implement simple variable renamings in this way.

Therefore we use the simple strategy to apply \texttt{subst} again
only in case of a substitution which was returned from \texttt{compose}.
\begin{verbatim}

substVar :: Subst v e => Subst v e -> v -> e
substVar (Subst comp sigma) v = maybe (var v) subst' (lookupFM v sigma)
  where subst' = if comp then subst (Subst comp sigma) else id

> compose :: (Show v,Ord v,Show e) => Subst v e -> Subst v e -> Subst v e
> compose sigma sigma' =
>   composed (foldr (uncurry bindSubst) sigma' (substToList sigma))
>   where dom = domain sigma
>         dom' = domain sigma'
>         domain = map fst . substToList
>         composed (Subst _ sigma) = Subst True sigma

\end{verbatim}
Unfortunately Haskell does not (yet) support multi-parameter type
classes. For that reason we have to define a separate class for each
kind of variable type for these functions. We implement
\texttt{substVar} as a function that takes the class functions as an
additional parameters. As an example for the use of this function the
module includes a class \texttt{IntSubst} for substitution whose
domain are integer numbers.
\begin{verbatim}

> substVar' :: Ord v => (v -> e) -> (Subst v e -> e -> e)
>           -> Subst v e -> v -> e
> substVar' var subst (Subst comp sigma) v =
>   maybe (var v) subst' (lookupFM v sigma)
>   where subst' = if comp then subst (Subst comp sigma) else id

> class IntSubst e where
>   ivar :: Int -> e
>   isubst :: Subst Int e -> e -> e

> isubstVar :: IntSubst e => Subst Int e -> Int -> e
> isubstVar = substVar' ivar isubst

\end{verbatim}
The function \texttt{restrictSubstTo} implements the restriction of a
substitution to a given subset of its domain.
\begin{verbatim}

> restrictSubstTo :: Ord v => [v] -> Subst v e -> Subst v e
> restrictSubstTo vs (Subst comp sigma) =
>   foldr (uncurry bindSubst) (Subst comp zeroFM)
>         (filter ((`elem` vs) . fst) (toListFM sigma))

\end{verbatim}
