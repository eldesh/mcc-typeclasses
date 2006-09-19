% -*- LaTeX -*-
% $Id: MachThreads.lhs 1744 2005-08-23 16:17:12Z wlux $
%
% Copyright (c) 1998-2003, Wolfgang Lux
% See LICENSE for the full license.
%
\subsubsection{Thread management}
The code implementing the management of threads is straight
forward. This module also provides the functions to save and restore
search continuations. These functions essentially return or update the
ready queue of the abstract machine.

The module maintains the invariant that the head of the ready queue
is never a thread surrogate for a thread that is already woken.
\begin{verbatim}

> module MachThreads(
>     newThread, runThread, interruptThread, yieldThread,
>     yieldSuspendThread, suspendThread, wakeThreads,
>     saveContinuation, restoreContinuation, resumeContinuation) where
> import MachTypes
> import Env
> import Maybe
> import Combined

> newThread :: Monad m => State -> m State
> newThread state =
>   return state{ tid = tid', env = emptyEnv, ds = [], rs = [], ct = tid' + 1 }
>   where tid' = ct state

> runThread :: RefMonad m => State -> m (Maybe Instruction,State)
> runThread state =
>   case rq state of
>     [] -> return (Nothing,state)
>     thd : rq ->
>       do
>         rq' <- cleanQueue rq
>         run thd state{ rq = rq' }
>   where run (Thread id ip env ds rs) state =
>           return (Just ip,state{ tid = id, env = env, ds = ds, rs = rs })
>         run (ThreadSurrogate _ ptr@(ThreadPtr rthd)) state =
>           do
>             thd <- readRef rthd
>             writeRef rthd Nothing
>             case thd of
>               Just thd ->
>                 run thd state{ tp = ThreadState ptr (Just thd) : tp state }
>               Nothing -> fail "Woken thread at head of ready-queue"

> interruptThread :: Monad m => Instruction -> State -> m State
> interruptThread next state =
>   do
>     thd <- suspendThread next state
>     return state{ rq = thd : rq state }

> yieldThread :: Monad m => Instruction -> State -> m (Bool,State)
> yieldThread next state
>   | null (rq state) = return (False,state)
>   | otherwise =
>       do
>         thd <- suspendThread next state
>         return (True,state{ rq = rq state ++ [thd] })

> yieldSuspendThread :: RefMonad m => Instruction -> State
>                    -> m (Maybe Thread,State)
> yieldSuspendThread next state
>   | null (rq state) = return (Nothing,state)
>   | otherwise =
>       do
>         thd <- suspendThread next state
>         sur <- surrogate thd
>         return (Just sur, state{ rq = rq state ++ [sur] })
>   where surrogate (Thread id ip env ds rs) =
>           do
>             rthd <- newRef (Just (Thread id ip env ds rs))
>             return (ThreadSurrogate id (ThreadPtr rthd))

> suspendThread :: Monad m => Instruction -> State -> m Thread
> suspendThread ip state =
>   return (Thread (tid state) ip (env state) (ds state) (rs state))

> wakeThreads :: RefMonad m => [Thread] -> State -> m State
> wakeThreads tq state =
>   do
>     tq' <- cleanQueue tq
>     return state{ rq = tq' ++ rq state }

> saveContinuation :: Monad m => State -> m ThreadQueue
> saveContinuation state = return (rq state)

> resumeContinuation :: Monad m => ThreadQueue -> State ->  m State
> resumeContinuation rq' state = return state{ rq = rq' }

> restoreContinuation :: Monad m => ThreadQueue -> State -> m State
> restoreContinuation rq' state = return state{ rq = rq' ++ rq state }

> cleanQueue :: RefMonad m => ThreadQueue -> m ThreadQueue
> cleanQueue tq = mapM cleanThread tq >>= return . catMaybes
>   where cleanThread thd =
>           case thd of
>             Thread _ _ _ _ _ -> return (Just thd)
>             ThreadSurrogate _ (ThreadPtr rthd) ->
>               readRef rthd >>= return . fmap (const thd)

\end{verbatim}
