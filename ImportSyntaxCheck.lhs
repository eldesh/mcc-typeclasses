% -*- LaTeX -*-
% $Id: ImportSyntaxCheck.lhs 3225 2016-06-16 08:40:29Z wlux $
%
% Copyright (c) 2000-2015, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{ImportSyntaxCheck.lhs}
\section{Checking Import Lists}
Before actually importing definitions into the current module, the
compiler first checks and expands the import specifications of all
import declarations.
\begin{verbatim}

> module ImportSyntaxCheck(checkImports) where
> import Applicative
> import Base
> import Curry
> import CurryUtils
> import Error
> import Env
> import IdentInfo
> import List
> import Maybe
> import PredefIdent
> import TopEnv
> import Utils

> checkImports :: Interface -> Maybe ImportSpec -> Error (Maybe ImportSpec)
> checkImports (Interface m _ ds) =
>   maybe (return Nothing) (liftA Just . expandSpecs m tEnv vEnv)
>   where tEnv = bindIdents tidents ds
>         vEnv = bindIdents vidents ds

\end{verbatim}
The compiler uses two environments collecting the type and value
identifiers, respectively, declared in the interface. In a first step,
the two export environments are initialized from the interface's
declarations.
\begin{verbatim}

> type ExpTypeEnv = Env Ident TypeKind
> type ExpFunEnv = Env Ident ValueKind

> bindIdents :: Entity a => (IDecl -> [a]) -> [IDecl] -> Env Ident a
> bindIdents idents ds = foldr bindIdent emptyEnv (concatMap idents ds)
>   where bindIdent x = bindEnv (unqualify (origName x)) x

\end{verbatim}
After the environments have been initialized, the optional import
specifications can be checked. There are two kinds of import
specifications, a ``normal'' one, which names the entities that shall
be imported, and a hiding specification, which lists those entities
that shall not be imported.

There is a subtle difference between both kinds of
specifications. While it is not allowed to list a data constructor
outside of its type in a ``normal'' specification, it is allowed to
hide a data constructor explicitly. E.g., if module \texttt{A} exports
the data type \texttt{T} with constructor \texttt{C}, the data
constructor can be imported with one of the two specifications
\begin{verbatim}
import A(T(C))
import A(T(..))
\end{verbatim}
but can be hidden in three different ways:
\begin{verbatim}
import A hiding(C)
import A hiding(T(C))
import A hiding(T(..))
\end{verbatim}

The functions \texttt{expandImport} and \texttt{expandHiding} check
that all entities in an import specification are actually exported
from the module. In addition, all imports of type constructors are
changed into a \texttt{T()} specification and explicit imports for the
data constructors are added. The code of \texttt{expandSpecs} ensures
that the unit, list, and tuple types are always imported from the
Prelude even if its imported entities are specified explicitly.
\begin{verbatim}

> expandSpecs :: ModuleIdent -> ExpTypeEnv -> ExpFunEnv -> ImportSpec
>             -> Error ImportSpec
> expandSpecs m tEnv vEnv (Importing p is) =
>   liftA (Importing p . (is' ++) . concat)
>         (mapA (expandImport p m tEnv vEnv) is)
>   where is' = [importType t | m == preludeMIdent,
>                               (tc,t) <- envToList tEnv, isPrimTypeId tc]
> expandSpecs m tEnv vEnv (Hiding p is) =
>   liftA (Hiding p . concat) (mapA (expandHiding p m tEnv vEnv) is)

> expandImport :: Position -> ModuleIdent -> ExpTypeEnv -> ExpFunEnv -> Import
>              -> Error [Import]
> expandImport p m tEnv vEnv (Import x) = expandThing p m tEnv vEnv x
> expandImport p m tEnv vEnv (ImportTypeWith tc xs) =
>   expandTypeWith p m tEnv tc xs
> expandImport p m tEnv vEnv (ImportTypeAll tc) = expandTypeAll p m tEnv tc

> expandHiding :: Position -> ModuleIdent -> ExpTypeEnv -> ExpFunEnv -> Import
>              -> Error [Import]
> expandHiding p m tEnv vEnv (Import x) = expandHide p m tEnv vEnv x
> expandHiding p m tEnv vEnv (ImportTypeWith tc xs) =
>   expandTypeWith p m tEnv tc xs
> expandHiding p m tEnv vEnv (ImportTypeAll tc) = expandTypeAll p m tEnv tc

> expandThing :: Position -> ModuleIdent -> ExpTypeEnv -> ExpFunEnv -> Ident
>             -> Error [Import]
> expandThing p m tEnv vEnv tc =
>   case lookupEnv tc tEnv of
>     Just _ -> expandThing' p m vEnv tc (Just [ImportTypeWith tc []])
>     Nothing -> expandThing' p m vEnv tc Nothing

> expandThing' :: Position -> ModuleIdent -> ExpFunEnv -> Ident
>              -> Maybe [Import] -> Error [Import]
> expandThing' p m vEnv f tcImport =
>   case lookupEnv f vEnv of
>     Just (Constr _) -> maybe (errorAt p (importDataConstr f)) return tcImport
>     Just (Var _ _) -> return (Import f : fromMaybe [] tcImport)
>     Nothing -> maybe (errorAt p (undefinedEntity m f)) return tcImport

> expandHide :: Position -> ModuleIdent -> ExpTypeEnv -> ExpFunEnv -> Ident
>            -> Error [Import]
> expandHide p m tEnv vEnv tc =
>   case lookupEnv tc tEnv of
>     Just _ -> expandHide' p m vEnv tc (Just [ImportTypeWith tc []])
>     Nothing -> expandHide' p m vEnv tc Nothing

> expandHide' :: Position -> ModuleIdent -> ExpFunEnv -> Ident
>             -> Maybe [Import] -> Error [Import]
> expandHide' p m vEnv f tcImport =
>   case lookupEnv f vEnv of
>     Just _ -> return (Import f : fromMaybe [] tcImport)
>     Nothing -> maybe (errorAt p (undefinedEntity m f)) return tcImport

> expandTypeWith :: Position -> ModuleIdent -> ExpTypeEnv -> Ident -> [Ident]
>                -> Error [Import]
> expandTypeWith p m tEnv tc xs =
>   do
>     (isType,xs'') <- elements p m tEnv tc
>     mapA_ (errorAt p . undefinedElement isType tc)
>           (filter (`notElem` xs'') xs')
>     return [ImportTypeWith tc xs']
>   where xs' = nub xs

> expandTypeAll :: Position -> ModuleIdent -> ExpTypeEnv -> Ident
>               -> Error [Import]
> expandTypeAll p m tEnv tc =
>   do
>     (_,xs) <- elements p m tEnv tc
>     return [ImportTypeWith tc xs]

> elements :: Position -> ModuleIdent -> ExpTypeEnv -> Ident
>          -> Error (Bool,[Ident])
> elements p m tEnv tc =
>   case lookupEnv tc tEnv of
>     Just (Data _ xs) -> return (True,xs)
>     Just (Alias _) -> return (True,[])
>     Just (Class _ fs) -> return (False,fs)
>     Nothing -> errorAt p (undefinedEntity m tc)

> importType :: TypeKind -> Import
> importType (Data tc xs) = ImportTypeWith (unqualify tc) xs
> importType (Alias tc) = ImportTypeWith (unqualify tc) []

\end{verbatim}
Error messages.
\begin{verbatim}

> undefinedEntity :: ModuleIdent -> Ident -> String
> undefinedEntity m x =
>   "Module " ++ moduleName m ++ " does not export " ++ name x

> undefinedElement :: Bool -> Ident -> Ident -> String
> undefinedElement True tc c =
>   name c ++ " is not a constructor or label of type " ++ name tc
> undefinedElement False cls f =
>   name f ++ " is not a method of type class " ++ name cls

> importDataConstr :: Ident -> String
> importDataConstr c = "Explicit import of data constructor " ++ name c

\end{verbatim}
