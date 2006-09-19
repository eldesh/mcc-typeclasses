% -*- LaTeX -*-
% $Id: MachNode.lhs 1744 2005-08-23 16:17:12Z wlux $
%
% Copyright (c) 2002, Wolfgang Lux
% See LICENSE for the full license.
%
\subsubsection{Nodes}
This module provides the basic operations for the allocation of new
nodes, for dereferencing nodes and for the update of nodes.
\begin{verbatim}

> module MachNode where
> import MachTypes
> import Combined

> atom :: RefMonad m => NodeTag -> State -> m (NodePtr,State)
> atom (ConstructorTag tag cName 0) = allocNode (ConstructorNode tag cName [])

> allocNode :: RefMonad m => Node -> State -> m (NodePtr,State)
> allocNode node state =
>   do
>     ref <- newRef node
>     return (Ptr adr ref,state{ hp = adr + 1 })
>   where adr = hp state

> allocNodes :: RefMonad m => [Node] -> State -> m ([NodePtr],State)
> allocNodes nodes state =
>   do
>     refs <- mapM newRef nodes
>     return (zipWith Ptr [adr..] refs,
>             state{ hp = adr + toInteger (length nodes) })
>   where adr = hp state

> deref :: RefMonad m => NodePtr -> m Node
> deref (Ptr _ ref) = readRef ref

> deref2 :: RefMonad m => (NodePtr,NodePtr) -> m (Node,Node)
> deref2 (ptr,ptr') =
>   deref ptr >>= \node -> deref ptr' >>= \node' -> return (node,node')

> derefPtr :: RefMonad m => NodePtr -> m NodePtr
> derefPtr (Ptr adr ref) = readRef ref >>= derefIndir
>   where derefIndir (IndirNode ptr) = derefPtr ptr
>         derefIndir _ = return (Ptr adr ref)

> updateNode :: RefMonad m => NodePtr -> Node -> m ()
> updateNode (Ptr _ ref) = writeRef ref

\end{verbatim}
