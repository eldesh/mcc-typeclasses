% -*- LaTeX -*-
% $Id: MachSpace.lhs 1893 2006-04-12 17:51:56Z wlux $
%
% Copyright (c) 1998-2006, Wolfgang Lux
% See LICENSE for the full license.
%
\subsubsection{Local search spaces}
\begin{verbatim}

> module MachSpace(curContext, pushSearchContext, popSearchContext,
>                  curSpace, isALocalSpace, isLocalSpaceOf, isRootSpace,
>                  newSearchSpace, saveSearchSpace, discardSearchSpace,
>                  restoreSearchSpace, actBindings) where
> import MachTypes
> import Env
> import Combined

\end{verbatim}
The function \texttt{curContext} returns the current search context.
This is used to determine whether the machine operates in a local or
global search and in the latter case if it is executing monadic code.
\begin{verbatim}

> curContext :: Monad m => State -> m SearchContext
> curContext state = return (sc state)

\end{verbatim}
When \texttt{try} is invoked, the current search context is saved and
a new search context is initialized using the supplied goal, variable,
and search space.
\begin{verbatim}

> pushSearchContext :: Monad m => NodePtr -> NodePtr -> SearchSpace
>                   -> State -> m State
> pushSearchContext goal var space state =
>   return state{ env = emptyEnv, ds = [], rs = [], rq = [], tp = [],
>                 sc = SearchContext goal var (tid state) (ds state) (rs state)
>                                    (rq state) (tp state)
>                                    (sc state) (ss state),
>                 ss = space }

> popSearchContext :: Monad m => State -> m ((NodePtr,NodePtr),State)
> popSearchContext state =
>   case sc state of
>     IOContext -> fail "Empty search context stack"
>     GlobalContext -> fail "Empty search context stack"
>     SearchContext goal var tid ds rs rq tp sc ss ->
>       return ((goal,var),
>               state{ tid = tid, env = emptyEnv, ds = ds, rs = rs,
>                      rq = rq, tp = tp, sc = sc, ss = ss })

\end{verbatim}
The function \texttt{curSpace} returns the current search space. The
predicate \texttt{isALocalSpace} tests whether the given search space
is the current local search space. Finally, \texttt{isLocalSpaceOf}
checks whether both arguments are derived from the same root space.
\begin{verbatim}

> curSpace :: Monad m => State -> m SearchSpace
> curSpace state = return (ss state)

> isALocalSpace :: RefMonad m => SearchSpace -> State -> m Bool
> isALocalSpace ptr state = ptr `isLocalSpaceOf` ss state

> isLocalSpaceOf :: RefMonad m => SearchSpace -> SearchSpace -> m Bool
> GlobalSpace `isLocalSpaceOf` GlobalSpace = return True
> GlobalSpace `isLocalSpaceOf` LocalSpace{} = return False
> LocalSpace{} `isLocalSpaceOf` GlobalSpace = return False
> LocalSpace{ root = rootRef } `isLocalSpaceOf` LocalSpace{ root = rootRef' } =
>   readRef rootRef >>= \root ->
>   readRef rootRef' >>= \root' ->
>   return (root == root')

\end{verbatim}
A new search space is created for every invocation of \texttt{try}.
The new search space will be its own root space and use the global
space as its parent. The trail and the script of the new space are
empty.
\begin{verbatim}

> newSearchSpace :: RefMonad m => State -> m (SearchSpace,State)
> newSearchSpace state =
>   do
>     rootRef <- newRef undefined
>     parentRef <- newRef GlobalSpace
>     activeRef <- newRef undefined
>     let newSpace = LocalSpace adr rootRef parentRef [] [] activeRef
>     writeRef rootRef newSpace
>     writeRef activeRef newSpace
>     return (newSpace,state{ hp = adr + 1 })
>   where adr = hp state

\end{verbatim}
When an encapsulated search returns with a solved goal or with a list
of alternative continuations, a new search space is created that saves
the current bindings of the local variables and suspend nodes. The new
space becomes a child of the current space.
\begin{verbatim}

> saveSearchSpace :: RefMonad m => State -> m (SearchSpace,State)
> saveSearchSpace state = save (ss state)
>   where save GlobalSpace = fail "Cannot save the global search space"
>         save parent@LocalSpace{ root = rootRef } =
>           do
>             parentRef <- newRef parent
>             activeRef <- newRef noActiveSpace
>             script <- saveBindings state
>             let newSpace = LocalSpace adr rootRef parentRef
>                                       (tp state) (reverse script) activeRef
>             readRef rootRef >>= flip writeRef newSpace . active
>             return (newSpace,state{ hp = adr + 1, ss = newSpace, tp = [] })
>           where adr = hp state

> noActiveSpace :: SearchSpace
> noActiveSpace = error "trying to determine active space of a non-root space"

\end{verbatim}
When an encapsulated search fails, the bindings recorded on the trail
are undone.
\begin{verbatim}

> discardSearchSpace :: RefMonad m => State -> m State
> discardSearchSpace state =
>   do
>     mapM_ undoBinding (tp state)
>     return state{ tp = [] }

\end{verbatim}
When a search space is restored, its bindings are activated again. In
addition, the current search space becomes a child of the restored
search space. However, this is possible only if the current search
space is a root space. The function \texttt{isRootSpace} can be used
to check this condition. Note that the global search space is not a
root space. Also note that the active search space pointer of the
current space becomes invalid, since it is no longer a root space.
\begin{verbatim}

> isRootSpace :: RefMonad m => SearchSpace -> m Bool
> isRootSpace GlobalSpace = return False
> isRootSpace space@LocalSpace{ parent = parentRef } =
>   readRef parentRef >>= return . (GlobalSpace ==)

> restoreSearchSpace :: RefMonad m => SearchSpace -> State -> m State
> restoreSearchSpace GlobalSpace state =
>   fail "Cannot restore global search space"
> restoreSearchSpace space state = restore (ss state)
>   where restore GlobalSpace =
>           fail "Cannot restore search space into global space"
>         restore curSpace@LocalSpace{ root = rootRef, parent = parentRef,
>                                      active = activeRef } =
>           readRef parentRef >>= return . (GlobalSpace ==) >>= \so ->
>           if so then
>             do
>               actBindings space
>               root <- readRef (root space)
>               writeRef rootRef root
>               writeRef parentRef space
>               writeRef activeRef noActiveSpace
>               writeRef (active root) curSpace
>               return state
>           else
>             fail "Cannot restore search space into non-root space"

\end{verbatim}
When a search space is restored, its bindings may not be in effect. In
that case we must undo the bindings of the active search space and its
ancestors from the same search space tree and then redo the bindings
of the restored space and all its ancestors. In fact, we do not need
to undo and redo up to the root, but only up to the closest common
ancestor.\footnote{The same optimization is also implemented in Amoz.}
\begin{verbatim}

> actBindings :: RefMonad m => SearchSpace -> m ()
> actBindings GlobalSpace = fail "Attempt to change to the global space"
> actBindings space = readRef (root space) >>= changeBindings space
>   where changeBindings space GlobalSpace = fail "Invalid root space"
>         changeBindings space LocalSpace{ active = activeRef } =
>           do
>             readRef activeRef >>= undoBindings
>             redoBindings space
>             writeRef activeRef space

\end{verbatim}
\ToDo{Implement the closest common ancestor optimization.}

Since in our implementation variables can be updated more than once,
we must be careful about the order in which the bindings of a search
space are undone and redone, otherwise wrong bindings might be
restored. Note that the bindings in the script are reversed when
saving them. Therefore, we do not need to reverse the script of a
search space while the bindings are redone.
\begin{verbatim}

> saveBindings :: RefMonad m => State -> m [UpdateInfo]
> saveBindings state = mapM saveBinding (tp state) >>= return . reverse

> saveBinding :: RefMonad m => UpdateInfo -> m UpdateInfo
> saveBinding (NodeBinding (Ptr adr ref) _) =
>   readRef ref >>= return . (NodeBinding (Ptr adr ref))
> saveBinding (ThreadState (ThreadPtr rthd) thd) =
>   readRef rthd >>= return . (ThreadState (ThreadPtr rthd))

> undoBindings :: RefMonad m => SearchSpace -> m ()
> undoBindings GlobalSpace = return ()
> undoBindings LocalSpace{ parent = parentRef, trail = trail } =
>   do
>     mapM_ undoBinding trail
>     readRef parentRef >>= undoBindings

> undoBinding :: RefMonad m => UpdateInfo -> m ()
> undoBinding (NodeBinding (Ptr _ ref) node) = writeRef ref node
> undoBinding (ThreadState (ThreadPtr rthd) thd) = writeRef rthd thd

> redoBindings :: RefMonad m => SearchSpace -> m ()
> redoBindings GlobalSpace = return ()
> redoBindings LocalSpace{ parent = parentRef, script = script } =
>   do
>     readRef parentRef >>= redoBindings
>     mapM_ redoBinding script

> redoBinding :: RefMonad m => UpdateInfo -> m ()
> redoBinding = undoBinding

\end{verbatim}
