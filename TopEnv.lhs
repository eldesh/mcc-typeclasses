% -*- LaTeX -*-
% $Id: TopEnv.lhs 2899 2009-08-24 09:52:45Z wlux $
%
% Copyright (c) 1999-2009, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{TopEnv.lhs}
\subsection{Top-Level Environments}\label{sec:toplevel-env}
The module \texttt{TopEnv} implements environments for qualified and
possibly ambiguous identifiers. An identifier is ambiguous if two
different entities are imported under the same name or if a local
definition uses the same name as an imported entity. Following an idea
presented in \cite{DiatchkiJonesHallgren02:ModuleSystem}, an
identifier is associated with a list of entities in order to handle
ambiguous names properly.

The code in this module ensures that the list of entities returned by
the functions \texttt{lookupTopEnv} and \texttt{qualLookupTopEnv}
contains exactly one element for each imported entity regardless of
how many times and from which modules it was imported. Thus, the
result of these function is a list with exactly one element if and
only if the identifier is unambiguous.
\begin{verbatim}

> module TopEnv(TopEnv, Entity(..), emptyTopEnv, importTopEnv, qualImportTopEnv,
>               bindTopEnv, globalBindTopEnv, localBindTopEnv, qualBindTopEnv,
>               rebindTopEnv, globalRebindTopEnv, localRebindTopEnv,
>               qualRebindTopEnv, localUnimportTopEnv, localUnbindTopEnv,
>               lookupTopEnv, qualLookupTopEnv, allEntities,
>               allImports, localBindings, moduleBindings) where
> import Env
> import Ident
> import Maybe
> import Utils

> newtype TopEnv a = TopEnv (Env QualIdent [(Source,a)]) deriving Show
> data Source = Local | Imported deriving (Eq,Show)

> instance Functor TopEnv where
>   fmap f (TopEnv env) = TopEnv (fmap (map (apSnd f)) env)

> bindEntities :: QualIdent -> [(Source,a)] -> Env QualIdent [(Source,a)]
>              -> Env QualIdent [(Source,a)]
> bindEntities x ys
>   | null ys = unbindEnv x
>   | otherwise = bindEnv x ys

> entities :: QualIdent -> Env QualIdent [(Source,a)] -> [(Source,a)]
> entities x env = fromMaybe [] (lookupEnv x env)

> emptyTopEnv :: TopEnv a
> emptyTopEnv = TopEnv emptyEnv

\end{verbatim}
In general, two entities are considered equal if the names of their
original definitions match.  However, in the case of algebraic data
types it is possible to hide some or all of their data constructors on
import and export, respectively. In this case we have to merge both
imports such that all data constructors which are visible through any
import path are visible in the current module. The class
\texttt{Entity} is used to handle this merge.
\begin{verbatim}

> class Entity a where
>  origName :: a -> QualIdent
>  merge    :: a -> a -> Maybe a
>  merge x y
>    | origName x == origName y = Just x
>    | otherwise = Nothing

\end{verbatim}
The function \texttt{importTopEnv} imports an entity from another
module into an environment. If the \texttt{qual}ified import flag is
\texttt{True}, only a binding for the qualified name is introduced
in the environment. Otherwise, both a qualified and an unqualified
import are performed.
\begin{verbatim}

> importTopEnv :: Entity a => Bool -> ModuleIdent -> Ident -> a
>              -> TopEnv a -> TopEnv a
> importTopEnv qual
>   | qual = qualImport
>   | otherwise = \m x y -> unqualImport x y . qualImport m x y
>   where unqualImport x = qualImportTopEnv (qualify x)
>         qualImport m x = qualImportTopEnv (qualifyWith m x)

> qualImportTopEnv :: Entity a => QualIdent -> a -> TopEnv a -> TopEnv a
> qualImportTopEnv x y (TopEnv env) =
>   TopEnv (bindEnv x (mergeImport y (entities x env)) env)

> mergeImport :: Entity a => a -> [(Source,a)] -> [(Source,a)]
> mergeImport x [] = [(Imported,x)]
> mergeImport x ((Local,x') : xs) = (Local,x') : mergeImport x xs
> mergeImport x ((Imported,x') : xs) =
>   case merge x x' of
>     Just x'' -> (Imported,x'') : xs
>     Nothing -> (Imported,x') : mergeImport x xs

\end{verbatim}
The function \texttt{globalBindTopEnv} introduces a binding for a
global definition into an environment. Such entities become visible
with an unqualified and a qualified name. The function
\texttt{localBindTopEnv} introduces a binding for a local definition
and binds only the unqualified name. After renaming has been applied,
the compiler can distinguish global and local identifiers by the value
of their renaming key. This allows using \texttt{bindTopEnv} to
introduce bindings for both global and local definitions.
\begin{verbatim}

> bindTopEnv :: ModuleIdent -> Ident -> a -> TopEnv a -> TopEnv a
> bindTopEnv m x
>   | isRenamed x = localBindTopEnv x
>   | otherwise = globalBindTopEnv m x

> globalBindTopEnv :: ModuleIdent -> Ident -> a -> TopEnv a -> TopEnv a
> globalBindTopEnv m x y =
>   localBindTopEnv x y . qualBindTopEnv (qualifyWith m x) y

> localBindTopEnv :: Ident -> a -> TopEnv a -> TopEnv a
> localBindTopEnv = qualBindTopEnv . qualify

> qualBindTopEnv :: QualIdent -> a -> TopEnv a -> TopEnv a
> qualBindTopEnv x y (TopEnv env) =
>   TopEnv (bindEnv x (bindLocal y (entities x env)) env)
>   where bindLocal x xs
>           | null [x' | (Local,x') <- xs] = (Local,x) : xs
>           | otherwise = error "internal error: qualBindTopEnv"

> rebindTopEnv :: ModuleIdent -> Ident -> a -> TopEnv a -> TopEnv a
> rebindTopEnv m x
>   | isRenamed x = localRebindTopEnv x
>   | otherwise = globalRebindTopEnv m x

> globalRebindTopEnv :: ModuleIdent -> Ident -> a -> TopEnv a -> TopEnv a
> globalRebindTopEnv m x y =
>   localRebindTopEnv x y . qualRebindTopEnv (qualifyWith m x) y

> localRebindTopEnv :: Ident -> a -> TopEnv a -> TopEnv a
> localRebindTopEnv = qualRebindTopEnv . qualify

> qualRebindTopEnv :: QualIdent -> a -> TopEnv a -> TopEnv a
> qualRebindTopEnv x y (TopEnv env) =
>   TopEnv (bindEnv x (rebindLocal (entities x env)) env)
>   where rebindLocal [] = error "internal error: qualRebindTopEnv"
>         rebindLocal ((Local,_) : ys) = (Local,y) : ys
>         rebindLocal ((Imported,y) : ys) = (Imported,y) : rebindLocal ys

> localUnimportTopEnv :: Ident -> TopEnv a -> TopEnv a
> localUnimportTopEnv x (TopEnv env) =
>   TopEnv (bindEntities x' (unbindImport (entities x' env)) env)
>   where x' = qualify x
>         unbindImport [] = []
>         unbindImport ((Local,y) : ys) = [(Local,y)]
>         unbindImport ((Imported,_) : ys) = unbindImport ys

> localUnbindTopEnv :: Ident -> TopEnv a -> TopEnv a
> localUnbindTopEnv x (TopEnv env) =
>   TopEnv (bindEntities x' (unbindLocal (entities x' env)) env)
>   where x' = qualify x
>         unbindLocal [] = error "internal error: unbindTopEnv"
>         unbindLocal ((Local,_) : ys) = ys
>         unbindLocal ((Imported,y) : ys) = (Imported,y) : unbindLocal ys

> lookupTopEnv :: Ident -> TopEnv a -> [a]
> lookupTopEnv = qualLookupTopEnv . qualify

> qualLookupTopEnv :: QualIdent -> TopEnv a -> [a]
> qualLookupTopEnv x (TopEnv env) = map snd (entities x env)

\end{verbatim}
The function \texttt{allEntities} returns a list of all entities bound
in an environment. The function \texttt{allImports} returns a list of
the names and values of all entities in an environment that were
imported from another module. The function \texttt{localBindings}
returns the list of all entities defined in the current module, and
the function \texttt{moduleBindings} returns the list of all entities
which are in scope with both an unqualified name $x$ and a qualified
name $M.x$. Since a name can be defined only once at the top-level of
a module and imports of the same entity are merged, the result lists
of both functions will contain no duplicates. Note that both functions
(actually, their help function \texttt{unqualBindings}) make use of
the fact that the list returned by \texttt{envToList} is sorted
according to the qualified names of the entities and qualified
identifiers are ordered first by their module qualifier.
\begin{verbatim}

> allEntities :: TopEnv a -> [a]
> allEntities (TopEnv env) =
>   [y | (x,ys) <- envToList env, isQualified x, (_,y) <- ys]

> allImports :: TopEnv a -> [(QualIdent,a)]
> allImports (TopEnv env) =
>   [(x,y) | (x,ys) <- envToList env, (Imported,y) <- ys]

> unqualBindings :: Maybe ModuleIdent -> TopEnv a -> [(Ident,(Source,a))]
> unqualBindings m (TopEnv env) =
>   [(x',y) | (x,ys) <- takeWhile p (dropWhile (not . p) (envToList env)),
>             let x' = unqualify x, y <- ys]
>   where p = (m ==) . fst . splitQualIdent . fst

> localBindings :: TopEnv a -> [(Ident,a)]
> localBindings env =
>   [(x,y) | (x,(Local,y)) <- unqualBindings Nothing env]

> moduleBindings :: Entity a => ModuleIdent -> TopEnv a -> [(Ident,a)]
> moduleBindings m env =
>   [(x',y) | (x',(_,y)) <- unqualBindings (Just m) env,
>             origName y `elem` map origName (lookupTopEnv x' env)]

\end{verbatim}
