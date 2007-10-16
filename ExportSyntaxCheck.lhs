% -*- LaTeX -*-
% $Id: ExportSyntaxCheck.lhs 2502 2007-10-16 20:10:53Z wlux $
%
% Copyright (c) 2000-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{ExportSyntaxCheck.lhs}
\section{Checking Module Export Lists}
The function \texttt{checkExports} checks the export specifications of
the module and expands them into a list containing all exported types
and functions, combining multiple exports for the same entity. The
expanded export specifications refer to the original names of all
entities.
\begin{verbatim}

> module ExportSyntaxCheck(checkExports) where
> import Base
> import CurrySyntax
> import Error
> import List
> import Map
> import Maybe
> import Set
> import TopEnv

> checkExports :: ModuleIdent -> [ImportDecl] -> TypeEnv -> FunEnv
>              -> Maybe ExportSpec -> Error ExportSpec
> checkExports m is tEnv fEnv =
>   maybe (return (nubExports (Exporting noPos (expandLocalModule tEnv fEnv))))
>         (\es -> do
>                   es' <- liftE nubExports (expandSpecs ms m tEnv fEnv es)
>                   checkInterface es'
>                   return es')
>   where ms = fromListSet [fromMaybe m asM | ImportDecl _ m _ asM _ <- is]
>         noPos = undefined

> checkInterface :: ExportSpec -> Error ()
> checkInterface (Exporting p es) =
>   mapE_ (errorAt p . ambiguousExport . fst)
>         (duplicates [unqualify tc | ExportTypeWith tc _ <- es]) &&>
>   mapE_ (errorAt p . ambiguousExport . fst)
>         (duplicates ([c | ExportTypeWith _ xs <- es, c <- xs] ++
>                      [unqualify f | Export f <- es]))

\end{verbatim}
While checking all export specifications, the compiler expands
specifications of the form \verb|T(..)| into
\texttt{T($C_1,\dots,C_n$)}, where $C_1,\dots,C_n$ are the data
constructors of type \texttt{T}, and replaces an export specification
\verb|module M| by specifications for all entities which are defined
in module \texttt{M} and imported into the current module with their
unqualified name. In order to distinguish exported type constructors
from exported functions, the former are translated into the equivalent
form \verb|T()|. Note that the export specification \texttt{x} may
export a type constructor \texttt{x} \emph{and} a global function
\texttt{x} at the same time.
\begin{verbatim}

> expandSpecs :: Set ModuleIdent -> ModuleIdent -> TypeEnv -> FunEnv
>             -> ExportSpec -> Error ExportSpec
> expandSpecs ms m tEnv fEnv (Exporting p es) =
>   liftE (Exporting p . concat) (mapE (expandExport p ms m tEnv fEnv) es)

> expandExport :: Position -> Set ModuleIdent -> ModuleIdent -> TypeEnv
>              -> FunEnv -> Export -> Error [Export]
> expandExport p _ _ tEnv fEnv (Export x) = expandThing p tEnv fEnv x
> expandExport p _ _ tEnv _ (ExportTypeWith tc xs) = expandTypeWith p tEnv tc xs
> expandExport p _ _ tEnv _ (ExportTypeAll tc) = expandTypeAll p tEnv tc
> expandExport p ms m tEnv fEnv (ExportModule m')
>   | m == m' =
>       return ((if m `elemSet` ms then expandModule tEnv fEnv m else []) ++
>               expandLocalModule tEnv fEnv)
>   | m' `elemSet` ms = return (expandModule tEnv fEnv m')
>   | otherwise = errorAt p (moduleNotImported m')

> expandThing :: Position -> TypeEnv -> FunEnv -> QualIdent -> Error [Export]
> expandThing p tEnv fEnv tc =
>   case qualLookupTopEnv tc tEnv of
>     [] -> expandThing' p fEnv tc Nothing
>     [t] -> expandThing' p fEnv tc (Just [exportType (abstract t)])
>       where abstract (Data tc _) = Data tc []
>             abstract (Alias tc) = Alias tc
>             abstract (Class cls _) = Class cls []
>     _ -> errorAt p (ambiguousName tc)

> expandThing' :: Position -> FunEnv -> QualIdent -> Maybe [Export]
>              -> Error [Export]
> expandThing' p fEnv f tcExport =
>   case qualLookupTopEnv f fEnv of
>     [] -> maybe (errorAt p (undefinedEntity f)) return tcExport
>     [Var f'] -> return (Export f' : fromMaybe [] tcExport)
>     [Constr _] -> maybe (errorAt p (exportDataConstr f)) return tcExport
>     _ -> errorAt p (ambiguousName f)

> expandTypeWith :: Position -> TypeEnv -> QualIdent -> [Ident]
>                -> Error [Export]
> expandTypeWith p tEnv tc xs =
>   do
>     (isType,tc',xs'') <- members p tEnv tc
>     mapE_ (errorAt p . undefinedElement isType tc)
>           (filter (`notElem` xs'') xs')
>     return [ExportTypeWith tc' xs']
>   where xs' = nub xs

> expandTypeAll :: Position -> TypeEnv -> QualIdent -> Error [Export]
> expandTypeAll p tEnv tc =
>   do
>     (_,tc',xs) <- members p tEnv tc
>     return [ExportTypeWith tc' xs]

> members :: Position -> TypeEnv -> QualIdent -> Error (Bool,QualIdent,[Ident])
> members p tEnv tc =
>   case qualLookupTopEnv tc tEnv of
>     [] -> errorAt p (undefinedEntity tc)
>     [Data tc cs] -> return (True,tc,cs)
>     [Alias tc] -> return (True,tc,[])
>     [Class cls fs] -> return (False,cls,fs)
>     _ -> errorAt p (ambiguousName tc)

> expandLocalModule :: TypeEnv -> FunEnv -> [Export]
> expandLocalModule tEnv fEnv =
>   [exportType t | (_,t) <- localBindings tEnv] ++
>   [Export f' | (f,Var f') <- localBindings fEnv, not (isRenamed f)]

> expandModule :: TypeEnv -> FunEnv -> ModuleIdent -> [Export]
> expandModule tEnv fEnv m =
>   [exportType t | (_,t) <- moduleImports m tEnv] ++
>   [Export f | (_,Var f) <- moduleImports m fEnv]

> exportType :: TypeKind -> Export
> exportType (Data tc cs) = ExportTypeWith tc cs
> exportType (Alias tc) = ExportTypeWith tc []
> exportType (Class cls fs) = ExportTypeWith cls fs

\end{verbatim}
The expanded list of exported entities may contain duplicates. These
are removed by the function \texttt{nubExports}. As a special case, if
a method is exported explicitly and along with its class, i.e., if
both $f$ and $C(\dots f \dots)$ appear in the export list, the
explicit export is removed. This ensures that the compiler generates
exactly the same interface file for the two equivalent modules
\texttt{module M((==), Eq((==))) where \lb \rb} and \texttt{module
  M(Eq((==))) where \lb \rb} and furthermore prevents the compiler
from reporting an ambiguous export.
\begin{verbatim}

> nubExports :: ExportSpec -> ExportSpec
> nubExports (Exporting p es) = Exporting p (ts ++ vs)
>   where ts = [ExportTypeWith tc xs | (tc,xs) <- types es]
>         fs = [qualifyLike tc x | ExportTypeWith tc xs <- ts, x <- xs]
>         vs = [Export f | f <- values es, f `notElem` fs]

> types :: [Export] -> [(QualIdent,[Ident])]
> types = toListFM . foldr addType zeroFM

> addType :: Export -> FM QualIdent [Ident] -> FM QualIdent [Ident]
> addType (Export _) tcs = tcs
> addType (ExportTypeWith tc xs) tcs =
>   addToFM tc (xs `union` fromMaybe [] (lookupFM tc tcs)) tcs

> values :: [Export] -> [QualIdent]
> values = toListSet . foldr addValue zeroSet

> addValue :: Export -> Set QualIdent -> Set QualIdent
> addValue (Export f) fs = f `addToSet` fs
> addValue (ExportTypeWith _ _) fs = fs

\end{verbatim}
Error messages.
\begin{verbatim}

> undefinedEntity :: QualIdent -> String
> undefinedEntity x =
>   "Entity " ++ qualName x ++ " in export list is not defined"

> moduleNotImported :: ModuleIdent -> String
> moduleNotImported m = "Module " ++ moduleName m ++ " not imported"

> ambiguousExport :: Ident -> String
> ambiguousExport x = "Ambiguous export of " ++ name x

> ambiguousName :: QualIdent -> String
> ambiguousName x = "Ambiguous name " ++ qualName x

> exportDataConstr :: QualIdent -> String
> exportDataConstr c = "Data constructor " ++ qualName c ++ " in export list"

> undefinedElement :: Bool -> QualIdent -> Ident -> String
> undefinedElement True tc c =
>   name c ++ " is not a data constructor of type " ++ qualName tc
> undefinedElement False cls f =
>   name f ++ " is not a method of type class " ++ qualName cls

\end{verbatim}
