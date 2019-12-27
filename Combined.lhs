% -*- LaTeX -*-
% $Id: Combined.lhs 3321 2019-12-27 10:56:53Z wlux $
%
% Copyright (c) 1998-2019, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Combined.lhs}
\section{Combined monads}\label{sec:combined-monads}
In this section we introduce combined monads which are parameterized
by another monads. This technique has been explored
in~\cite{KingWadler93:Combining} and very extensively
in~\cite{LiangHudakJones95:ModInterp}. The monad transformers used in
this report are mostly copied from the latter. Some restrictions were
necessary because Haskell~98 does not support multi-parameter type
classes. Especially, we cannot define generic lift operations because
they have to be parameterized over two monad classes. In addition, we
cannot define generic state and environment monad classes.
\begin{verbatim}

> module Combined where
> import Applicative
> import Error
> import Monad
> import IO
> import IOExts

\end{verbatim}
\subsection{Identity monad}
The identity monad only serves as a base monad if no other monad --
usually either \texttt{[]} or \texttt{IO} -- can be used. It allows
deriving the usual -- i.e. unparameterized -- state and environment
monads.
\begin{verbatim}

> newtype Id a = Id a

> unId :: Id a -> a
> unId (Id x) = x

> instance Functor Id where
>   fmap f (Id x) = Id (f x)

> instance Applicative Id where
>   pure x = Id x
>   Id f <*> Id x = Id (f x)

> instance Monad Id where
>   return x = Id x
>   Id x >>= k = k x

> callId :: Id a -> a
> callId = unId

\end{verbatim}
\subsection{State transformers}
The state transformer monad is defined as usual, except that the
result of the state transformer function is itself a monad. The
unparameterized version is defined by using the identity monad
\texttt{Id} for the base monad.
\begin{verbatim}

> newtype StateT s m a = StateT (s -> m (a,s))
> type St s a = StateT s Id a

> unStateT :: StateT s m a -> (s -> m (a,s))
> unStateT (StateT st) = st

> instance Functor f => Functor (StateT s f) where
>   fmap f (StateT st) = StateT (fmap (\(x,s') -> (f x,s')) . st)

> instance (Functor m,Monad m) => Applicative (StateT s m) where
>   pure = return
>   (<*>) = ap

> instance Monad m => Monad (StateT s m) where
>   return x = StateT (\s -> return (x,s))
>   StateT st >>= f = StateT (\s -> st s >>= \(x,s') -> unStateT (f x) s')
>   fail msg = StateT (const (fail msg))

> instance (Alternative m,Monad m) => Alternative (StateT s m) where
>   empty = StateT (const empty)
>   StateT st1 <|> StateT st2 = StateT (\s -> st1 s <|> st2 s)

> instance MonadPlus m => MonadPlus (StateT s m) where
>   mzero = StateT (const mzero)
>   StateT st1 `mplus` StateT st2 = StateT (\s -> st1 s `mplus` st2 s)

> liftSt :: Monad m => m a -> StateT s m a
> liftSt m = StateT (\s -> m >>= \x -> return (x,s))

> callSt :: Monad m => StateT s m a -> s -> m a
> callSt (StateT st) s = st s >>= return . fst

> runSt :: St s a -> s -> a
> runSt st = callId . callSt st

\end{verbatim}
In addition to the standard monad functions, state monads should
provide means to fetch and change the state. With multi-parameter type
classes, one could use the following class:
\begin{verbatim}

class Monad m => StateMonad s m where
  update :: (s -> s) -> m s
  fetch :: m s
  change :: s -> m s

  fetch = update id
  change = update . const

instance Monad m => StateMonad s (StateT s m) where
  update f = StateT (\s -> return (s,f s))

\end{verbatim}
Unfortunately multi-parameter type classes are not available in
Haskell~98. Therefore we define the corresponding instance functions
for each state monad class separately. Here are the functions for the
state transformers.
\begin{verbatim}

> updateSt :: Monad m => (s -> s) -> StateT s m s
> updateSt f = StateT (\s -> return (s,f s))

> updateSt_ :: Monad m => (s -> s) -> StateT s m ()
> updateSt_ f = StateT (\s -> return ((),f s))

> fetchSt :: Monad m => StateT s m s
> fetchSt = updateSt id

> changeSt :: Monad m => s -> StateT s m s
> changeSt = updateSt . const

> mapStateSt :: Monad m => (m (a,s) -> m (b,s)) -> StateT s m a -> StateT s m b
> mapStateSt f (StateT st) = StateT (\s -> f (st s))

\end{verbatim}
Currying and uncurrying for state monads has been implemented
in~\cite{Fokker95:JPEG}. Here we extend this implementation to the
parametric monad classes.
\begin{verbatim}

> stCurry :: Monad m => StateT (s,t) m a -> t -> StateT s m (t,a)
> stCurry (StateT st) t =
>   StateT (\s -> st (s,t) >>= \(x,(s',t')) -> return ((t',x),s'))

> stUncurry :: Monad m => (t -> StateT s m (t,a)) -> StateT (s,t) m a
> stUncurry f =
>   StateT (\(s,t) -> let (StateT st) = f t
>                     in st s >>= \((t',x),s') -> return (x,(s',t')))

\end{verbatim}
\subsection{Environment monad}
A variant of the state transformer monad is the environment monad
which is also known as (state) reader monad.
\begin{verbatim}

> newtype ReaderT r m a = ReaderT (r -> m a)
> type Rt r a = ReaderT r Id a

> unReaderT :: ReaderT r m a -> (r -> m a)
> unReaderT (ReaderT rt) = rt

> instance Functor f => Functor (ReaderT r f) where
>   fmap f (ReaderT rt) = ReaderT (fmap f . rt)

> instance Applicative f => Applicative (ReaderT r f) where
>   pure x = ReaderT (\_ -> pure x)
>   ReaderT rt1 <*> ReaderT rt2 = ReaderT (\r -> rt1 r <*> rt2 r)

> instance Monad m => Monad (ReaderT r m) where
>   return x = ReaderT (\_ -> return x)
>   ReaderT rt >>= f = ReaderT (\r -> rt r >>= \x -> unReaderT (f x) r)
>   fail msg = ReaderT (const (fail msg))

> instance Alternative f => Alternative (ReaderT r f) where
>   empty = ReaderT (\_ -> empty)
>   ReaderT rt <|> ReaderT rt' = ReaderT (\r -> rt r <|> rt' r)

> instance MonadPlus m => MonadPlus (ReaderT r m) where
>   mzero = ReaderT (\_ -> mzero)
>   ReaderT rt `mplus` ReaderT rt' = ReaderT (\r -> rt r `mplus` rt' r)

> liftRt :: Monad m => m a -> ReaderT r m a
> liftRt m = ReaderT (\_ -> m)

> callRt :: ReaderT r m a -> r -> m a
> callRt (ReaderT rt) r = rt r

> runRt :: Rt r a -> r -> a
> runRt rt = callId . callRt rt

\end{verbatim}
Similar to the state monad class, an environment monad class which
provides functions to access the current state and to run an
environment monad in a given state could be defined as follows:
\begin{verbatim}

class Monad m => EnvMonad r m where
  env :: m r
  putEnv :: r -> m a -> m a

instance Monad m => EnvMonad r (ReaderT r m) where
  env = ReaderT return
  putEnv r (ReaderT rt) = ReaderT (\_ -> rt r)

\end{verbatim}
Again, this requires multi-parameter type classes; thus we define the
appropriate instance functions for the type \texttt{ReaderT} instead.
\begin{verbatim}

> envRt :: Monad m => ReaderT r m r
> envRt = ReaderT return 

> putEnvRt :: Monad m => r -> ReaderT r m a -> ReaderT r m a
> putEnvRt r (ReaderT rt) = ReaderT (\_ -> rt r)

> mapEnvRt :: Monad m => (r -> r) -> ReaderT r m a -> ReaderT r m a
> mapEnvRt f (ReaderT rt) = ReaderT (\r -> rt (f r))

\end{verbatim}
Currying can also be applied to state reader monads.
\begin{verbatim}

> rtCurry :: Monad m => ReaderT (r,t) m a -> t -> ReaderT r m a
> rtCurry (ReaderT rt) t = ReaderT (\r -> rt (r,t))

> rtUncurry :: Monad m => (t -> ReaderT r m a) -> ReaderT (r,t) m a
> rtUncurry f = ReaderT (\(r,t) -> let (ReaderT rt) = f t in rt r)

\end{verbatim}
A state reader transformer can be transformed trivially into a state
transformer monad. This is handled by the combinator \texttt{ro}.
\begin{verbatim}

> ro :: Monad m => ReaderT r m a -> StateT r m a
> ro (ReaderT rt) = StateT (\s -> rt s >>= \x -> return (x,s))

\end{verbatim}
\subsection{Error monad}
Another useful monad defined in~\cite{LiangHudakJones95:ModInterp} is
the error monad.
\begin{verbatim}

> newtype ErrorT m a = ErrorT (m (Error a))

> unErrorT :: ErrorT m a -> m (Error a)
> unErrorT (ErrorT m) = m

> instance Functor f => Functor (ErrorT f) where
>   fmap f (ErrorT m) = ErrorT (fmap (fmap f) m)

> instance Applicative f => Applicative (ErrorT f) where
>   pure = ErrorT . pure . pure
>   ErrorT m1 <*> ErrorT m2 = ErrorT ((<*>) <$> m1 <*> m2)

> instance Monad m => Monad (ErrorT m) where
>   return = ErrorT . return . return
>   fail = ErrorT . return . fail
>   ErrorT m >>= f = ErrorT (m >>= k)
>     where k (Ok x) = unErrorT (f x)
>           k (Errors msgs) = return (Errors msgs)

> instance Alternative f => Alternative (ErrorT f) where
>   empty = ErrorT empty
>   ErrorT m1 <|> ErrorT m2 = ErrorT (m1 <|> m2)

> instance MonadPlus m => MonadPlus (ErrorT m) where
>   mzero = ErrorT mzero
>   ErrorT m1 `mplus` ErrorT m2 = ErrorT (m1 `mplus` m2)

> liftErr :: Monad m => m a -> ErrorT m a
> liftErr = ErrorT . liftM Ok

> callErr :: ErrorT m a -> m (Error a)
> callErr = unErrorT

\end{verbatim}
\subsection{Mutable variables}
All major Haskell implementations provide some kind of mutable state
variables. In order to be able to lift these operations to the
combined monads approach, we define a class for handling these
references. Currently this is restricted to the use of mutable
variables in the \texttt{IO} monad.\footnote{We use the interface
provided by Hugs and ghc and provide compatibility implementations for
hbc and nhc that adapt the respective implementations to the one used
here. See appendix~\ref{sec:hbc-ioexts} and~\ref{sec:nhc-ioexts} for
details.}
\begin{verbatim}

> type Ref a = IORef a

> class Monad m => RefMonad m where
>   newRef :: a -> m (Ref a)
>   readRef :: Ref a -> m a
>   writeRef :: Ref a -> a -> m ()

> instance RefMonad IO where
>   newRef = newIORef
>   readRef = readIORef
>   writeRef = writeIORef

\end{verbatim}
\subsection{Lifting operations}
In order to use the operations of one the classes defined above in
another monad, the appropriate \texttt{lift}\dots{} combinators have
to be applied. The following instance declarations automatically
provide these lifting operations. Unfortunately we cannot define such
implicit lifting operations for neither the state monad functions nor
the environment monad functions as we were unable to define those
classes.
\begin{verbatim}

> -- Reference monad
> instance RefMonad m => RefMonad (ErrorT m) where
>   newRef = liftErr . newRef
>   readRef = liftErr . readRef
>   writeRef ref = liftErr . writeRef ref

> instance RefMonad m => RefMonad (ReaderT s m) where
>   newRef = liftRt . newRef
>   readRef = liftRt . readRef
>   writeRef ref = liftRt . writeRef ref

> instance RefMonad m => RefMonad (StateT s m) where
>   newRef = liftSt . newRef
>   readRef = liftSt . readRef
>   writeRef ref = liftSt . writeRef ref

\end{verbatim}
