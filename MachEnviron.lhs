% -*- LaTeX -*-
% $Id: MachEnviron.lhs 1744 2005-08-23 16:17:12Z wlux $
%
% Copyright (c) 1998-2003, Wolfgang Lux
% See LICENSE for the full license.
%
\subsubsection{Environment management}
The following module provides the functions which access and update
the local environment.
\begin{verbatim}

> module MachEnviron(initEnv,getVar,getVars,setVar,setVars) where
> import MachTypes
> import Env
> import Utils

> initEnv :: Monad m => State -> m State
> initEnv state = return state{ env = emptyEnv }

> getVar :: Monad m => String -> State -> m NodePtr
> getVar v state = lookupVar v (env state)

> getVars :: Monad m => [String] -> State -> m [NodePtr]
> getVars vs state = mapM (flip lookupVar (env state)) vs

> setVar :: Monad m => String -> NodePtr -> State -> m State
> setVar v p state = return state{ env = bindEnv v p (env state) }

> setVars :: Monad m => [String] -> [NodePtr] -> State -> m State
> setVars vs ps state = return state{ env = foldr2 bindEnv (env state) vs ps }

> lookupVar :: Monad m => String -> LocalEnv -> m NodePtr
> lookupVar v env =
>   maybe (fail ("Unbound variable " ++ v)) return (lookupEnv v env)

\end{verbatim}
