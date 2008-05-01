% -*- LaTeX -*-
% $Id: TopEnv.lhs 2690 2008-05-01 20:40:17Z wlux $
%
% Copyright (c) 1999-2008, Wolfgang Lux
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

Tuple constructors must be treated specially because there is a
potentially unlimited number of them. Instead of inserting tuple
constructors into the environment, the compiler can optionally supply
an infinite list with information about tuple constructors when a new
environment is constructed with \texttt{emptyEnv}. Given a tuple
constructor with arity $n$, whose binding is not found in the
environment, the functions \texttt{lookupTopEnv} and
\texttt{qualLookupTopEnv} will return the element at index $n-2$ from
this list. Since the list is infinite, \texttt{TopEnv}'s \texttt{Show}
instance shows only the head of the list.

The code in this module ensures that the list of entities returned by
the functions \texttt{lookupTopEnv} and \texttt{qualLookupTopEnv}
contains exactly one element for each imported entity regardless of
how many times and from which modules it was imported. Thus, the
result of these function is a list with exactly one element if and
only if the identifier is unambiguous. The module names associated
with an imported entity identify the modules from which the entity was
imported.
\begin{verbatim}

> module TopEnv(TopEnv, Entity(..), emptyTopEnv, predefTopEnv,
>               importTopEnv, qualImportTopEnv,
>               bindTopEnv, globalBindTopEnv, localBindTopEnv, qualBindTopEnv,
>               rebindTopEnv, globalRebindTopEnv, localRebindTopEnv,
>               qualRebindTopEnv, localUnimportTopEnv, localUnbindTopEnv,
>               lookupTopEnv, qualLookupTopEnv, allEntities,
>               allImports, moduleImports, localBindings) where
> import Env
> import Ident
> import Maybe
> import PredefIdent
> import Utils

> data TopEnv a = TopEnv (Maybe [a]) (Env QualIdent [(Source,a)])
> data Source = Local | Import [ModuleIdent] deriving (Eq,Show)

> instance Show a => Show (TopEnv a) where
>   showsPrec p (TopEnv tup env) =
>     showParen (p > 10)
>               (showString "TopEnv " . showsPrec 11 (fmap head tup) .
>                showChar ' ' . showsPrec 11 env)

> instance Functor TopEnv where
>   fmap f (TopEnv tup env) =
>     TopEnv (fmap (map f) tup) (fmap (map (apSnd f)) env)

> bindEntities :: QualIdent -> [(Source,a)] -> Env QualIdent [(Source,a)]
>              -> Env QualIdent [(Source,a)]
> bindEntities x ys
>   | null ys = unbindEnv x
>   | otherwise = bindEnv x ys

> entities :: QualIdent -> Env QualIdent [(Source,a)] -> [(Source,a)]
> entities x env = fromMaybe [] (lookupEnv x env)

> emptyTopEnv :: Maybe [a] -> TopEnv a
> emptyTopEnv tup = TopEnv tup emptyEnv

> predefTopEnv :: Entity a => QualIdent -> a -> TopEnv a -> TopEnv a
> predefTopEnv x y (TopEnv tup env) =
>   case lookupEnv x env of
>     Just _ -> error "internal error: predefTopEnv"
>     Nothing -> TopEnv tup (bindEnv x [(Import [],y)] env)

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
>   | qual = qualImportTopEnv
>   | otherwise = \m x y -> unqualImportTopEnv m x y . qualImportTopEnv m x y

> unqualImportTopEnv :: Entity a => ModuleIdent -> Ident -> a
>                    -> TopEnv a -> TopEnv a
> unqualImportTopEnv m x y (TopEnv tup env) =
>   TopEnv tup (bindEnv x' (mergeImport m y (entities x' env)) env)
>   where x' = qualify x

> qualImportTopEnv :: Entity a => ModuleIdent -> Ident -> a -> TopEnv a
>                  -> TopEnv a
> qualImportTopEnv m x y (TopEnv tup env) =
>   TopEnv tup (bindEnv x' (mergeImport m y (entities x' env)) env)
>   where x' = qualifyWith m x

> mergeImport :: Entity a => ModuleIdent -> a -> [(Source,a)] -> [(Source,a)]
> mergeImport m x [] = [(Import [m],x)]
> mergeImport m x ((Local,x') : xs) = (Local,x') : mergeImport m x xs
> mergeImport m x ((Import ms,x') : xs) =
>   case merge x x' of
>     Just x'' -> (Import (m:ms),x'') : xs
>     Nothing -> (Import ms,x') : mergeImport m x xs

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
> qualBindTopEnv x y (TopEnv tup env) =
>   TopEnv tup (bindEnv x (bindLocal y (entities x env)) env)
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
> qualRebindTopEnv x y (TopEnv tup env) =
>   TopEnv tup (bindEnv x (rebindLocal (entities x env)) env)
>   where rebindLocal [] = error "internal error: qualRebindTopEnv"
>         rebindLocal ((Local,_) : ys) = (Local,y) : ys
>         rebindLocal ((Import ms,y) : ys) = (Import ms,y) : rebindLocal ys

> localUnimportTopEnv :: Ident -> TopEnv a -> TopEnv a
> localUnimportTopEnv x (TopEnv tup env) =
>   TopEnv tup (bindEntities x' (unbindImport (entities x' env)) env)
>   where x' = qualify x
>         unbindImport [] = []
>         unbindImport ((Local,y) : ys) = [(Local,y)]
>         unbindImport ((Import _,_) : ys) = unbindImport ys

> localUnbindTopEnv :: Ident -> TopEnv a -> TopEnv a
> localUnbindTopEnv x (TopEnv tup env) =
>   TopEnv tup (bindEntities x' (unbindLocal (entities x' env)) env)
>   where x' = qualify x
>         unbindLocal [] = error "internal error: unbindTopEnv"
>         unbindLocal ((Local,_) : ys) = ys
>         unbindLocal ((Import ms,y) : ys) = (Import ms,y) : unbindLocal ys

> lookupTopEnv :: Ident -> TopEnv a -> [a]
> lookupTopEnv = qualLookupTopEnv . qualify

> qualLookupTopEnv :: QualIdent -> TopEnv a -> [a]
> qualLookupTopEnv x (TopEnv tup env) =
>   map snd (entities x env) ++!
>   maybe [] (\ys -> [ys !! (qTupleArity x - 2) | isQTupleId x]) tup

\end{verbatim}
The function \texttt{allEntities} returns a list of all entities bound
in an environment. The function \texttt{allImports} returns a list of
the names and values of all entities in an environment that were
imported from another module. The functions \texttt{localBindings} and
\texttt{moduleImports} return the list of entities defined in the
current module and imported from a particular module, respectively.
Since a name can be defined only once at the top-level of a module and
imports of the same entity are merged, the result lists of both
functions will contain no duplicates.
\begin{verbatim}

> allEntities :: TopEnv a -> [a]
> allEntities (TopEnv _ env) =
>   [y | (x,ys) <- envToList env, isQualified x, (_,y) <- ys]

> allImports :: TopEnv a -> [(QualIdent,a)]
> allImports (TopEnv _ env) =
>   [(x,y) | (x,ys) <- envToList env, (Import _,y) <- ys]

> unqualBindings :: TopEnv a -> [(Ident,(Source,a))]
> unqualBindings (TopEnv _ env) =
>   [(x',y) | (x,ys) <- takeWhile (not . isQualified . fst) (envToList env),
>             let x' = unqualify x, y <- ys]

> moduleImports :: ModuleIdent -> TopEnv a -> [(Ident,a)]
> moduleImports m env =
>   [(x,y) | (x,(Import ms,y)) <- unqualBindings env, m `elem` ms]

> localBindings :: TopEnv a -> [(Ident,a)]
> localBindings env = [(x,y) | (x,(Local,y)) <- unqualBindings env]

\end{verbatim}
