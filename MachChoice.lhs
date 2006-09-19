% -*- LaTeX -*-
% $Id: MachChoice.lhs 1744 2005-08-23 16:17:12Z wlux $
%
% Copyright (c) 1998-2003, Wolfgang Lux
% See LICENSE for the full license.
%
\subsubsection{Choicepoints and backtracking}
Our choicepoint management provides the functions to create and drop
choicepoints, to update the continuation address of a choicepoint and
to backtrack to the topmost choicepoint.
\begin{verbatim}

> module MachChoice where
> import MachTypes
> import Combined

> pushChoicepoint :: Monad m => Instruction -> State -> m State
> pushChoicepoint ip state =
>   return state{ bp = choicepoint : bp state, tp = [] }
>   where choicepoint = Choicepoint ip (tid state) (env state) (ds state)
>                                   (rs state) (rq state) (tp state)

> updateChoicepoint :: Monad m => Instruction -> State -> m State
> updateChoicepoint ip state =
>   case bp state of
>     [] -> fail "Empty choicepoint stack"
>     Choicepoint _ tid env ds rs rq tp : bp ->
>       return state{ bp = Choicepoint ip tid env ds rs rq tp : bp }

> popChoicepoint :: Monad m => State -> m State
> popChoicepoint state =
>   case bp state of
>     [] -> fail "Empty choicepoint stack"
>     Choicepoint _ _ _ _ _ _ tp : bp -> return state{ bp = bp, tp = tp }

> backtrack :: RefMonad m => State -> m (Maybe Instruction,State)
> backtrack state =
>   case bp state of
>     [] -> return (Nothing,state)
>     Choicepoint ip tid env ds rs rq _ : _ ->
>       do
>         mapM_ restoreBinding (tp state)
>         return (Just ip,
>                 state{ tid = tid, env = env, ds = ds, rs = rs,
>                        rq = rq, tp = [] })
>   where restoreBinding (NodeBinding (Ptr _ ref) node) = writeRef ref node
>         restoreBinding (ThreadState (ThreadPtr rthd) thd) = writeRef rthd thd

> saveBinding :: Monad m => NodePtr -> Node -> State -> m State
> saveBinding ptr node state =
>   return state{ tp = NodeBinding ptr node : tp state }

\end{verbatim}
