% -*- LaTeX -*-
% $Id: SCC.lhs 1744 2005-08-23 16:17:12Z wlux $
%
% Copyright (c) 2000,2002-2003, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{SCC.lhs}
\section{Computing strongly connected components}
At various places in the compiler we had to partition a list of
declarations into strongly connected components. The function
\texttt{scc} computes this relation in two steps. First, the list is
topologically sorted ``downwards'' using the \emph{defs} relation.
Then the resulting list is sorted ``upwards'' using the \emph{uses}
relation and partitioned into the connected components. Both relations
are computed within this module using the bound and free names of each
declaration.

In order to avoid useless recomputations, the code in the module first
decorates the declarations with their bound and free names and a
unique number. The latter is only used to provide a trivial ordering
so that the declarations can be used as set elements.
\begin{verbatim}

> module SCC(scc) where
> import Set

> data Node a b = Node{ key::Int, bvs::[b], fvs::[b], node::a }

> instance Eq (Node a b) where
>   n1 == n2 = key n1 == key n2
> instance Ord (Node b a) where
>   n1 `compare` n2 = key n1 `compare` key n2

> scc :: Eq b => (a -> [b])              -- entities defined by node
>             -> (a -> [b])              -- entities used by node
>             -> [a]                     -- list of nodes
>             -> [[a]]                   -- strongly connected components
> scc bvs fvs = map (map node) . tsort' . tsort . zipWith wrap [0..]
>   where wrap i n = Node i (bvs n) (fvs n) n

> tsort :: Eq b => [Node a b] -> [Node a b]
> tsort xs = snd (dfs xs zeroSet [])
>   where dfs [] marks stack = (marks,stack)
>         dfs (x:xs) marks stack
>           | x `elemSet` marks = dfs xs marks stack
>           | otherwise = dfs xs marks' (x:stack')
>           where (marks',stack') = dfs (defs x) (x `addToSet` marks) stack
>         defs x = filter (any (`elem` fvs x) . bvs) xs

> tsort' :: Eq b => [Node a b] -> [[Node a b]]
> tsort' xs = snd (dfs xs zeroSet [])
>   where dfs [] marks stack = (marks,stack)
>         dfs (x:xs) marks stack
>           | x `elemSet` marks = dfs xs marks stack
>           | otherwise = dfs xs marks' ((x:concat stack'):stack)
>           where (marks',stack') = dfs (uses x) (x `addToSet` marks) []
>         uses x = filter (any (`elem` bvs x) . fvs) xs

\end{verbatim}
