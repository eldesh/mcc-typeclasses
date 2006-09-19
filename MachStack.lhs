% -*- LaTeX -*-
% $Id: MachStack.lhs 1744 2005-08-23 16:17:12Z wlux $
%
% Copyright (c) 1998-2003, Wolfgang Lux
% See LICENSE for the full license.
%
\subsubsection{Stack management}
This module provides the primitive operations for the management of
the data and return stacks.
\begin{verbatim}

> module MachStack where
> import MachTypes

> pushNode :: Monad m => NodePtr -> State -> m State
> pushNode node state = return state{ ds = node : ds state }

> pushNodes :: Monad m => [NodePtr] -> State -> m State
> pushNodes nodes state = return state{ ds = nodes ++ ds state }

> topNode :: Monad m => State -> m NodePtr
> topNode state =
>   case ds state of
>     []    -> fail "Empty data stack"
>     ptr:_ -> return ptr

> popNode :: Monad m => State -> m (NodePtr,State)
> popNode state =
>   case ds state of
>     []     -> fail "Empty data stack"
>     ptr:ds -> return (ptr,state{ ds = ds })

> popNodes2 :: Monad m => State -> m ((NodePtr,NodePtr),State)
> popNodes2 state =
>   case ds state of
>     []          -> fail "Empty data stack"
>     [ptr]       -> fail "Only one node in data stack"
>     ptr:ptr':ds -> return ((ptr,ptr'),state{ ds = ds })

> popNodes :: Monad m => Int -> State -> m ([NodePtr],State)
> popNodes n state
>   | n <= length stack = return (ptrs,state{ ds = ds' })
>   | otherwise         = fail "Too few nodes in data stack"
>   where stack = ds state
>         (ptrs,ds') = splitAt n stack

> pushCont :: Monad m => Instruction -> State -> m State
> pushCont ip state = return state{ rs = Cont ip (env state) : rs state }

> popCont :: Monad m => State -> m (Maybe Instruction,State)
> popCont state =
>   case rs state of
>     [] -> return (Nothing,state)
>     Cont ip env : rs -> return (Just ip,state{ env = env, rs = rs })

\end{verbatim}
