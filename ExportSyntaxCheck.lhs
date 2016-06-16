% -*- LaTeX -*-
% $Id: ExportSyntaxCheck.lhs 3225 2016-06-16 08:40:29Z wlux $
%
% Copyright (c) 2000-2015, Wolfgang Lux
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
> import Applicative
> import Base
> import Curry
> import Error
> import IdentInfo
> import List
> import Map
> import Maybe
> import PredefIdent
> import Set
> import TopEnv
> import Utils

> checkExports :: ModuleIdent -> [ImportDecl] -> TypeEnv -> FunEnv
>              -> Maybe ExportSpec -> Error ExportSpec
> checkExports m is tEnv fEnv es =
>   do
>     es' <-
>       liftA (nubExports . canonExports tEnv) (expandSpecs ms m tEnv fEnv es)
>     checkInterface es'
>     return es'
>   where ms = fromListSet [fromMaybe m asM | ImportDecl _ m _ asM _ <- is]

> checkInterface :: ExportSpec -> Error ()
> checkInterface (Exporting p es) =
>   mapA_ (errorAt p . ambiguousExport . fst)
>         (duplicates [unqualify tc | ExportTypeWith tc _ <- es]) *>
>   mapA_ (errorAt p . ambiguousExport . fst)
>         (duplicates ([x | ExportTypeWith _ xs <- es, x <- xs] ++
>                      [unqualify f | Export f <- es]))

\end{verbatim}
While checking all export specifications, the compiler expands
specifications of the form \verb|T(..)| and \verb|C(..)| into
\texttt{T($C_1,\dots,C_m,l_1,\dots,l_n$)}, where $C_1,\dots,C_m$ are
the data constructors of type \texttt{T} and $l_1,\dots,l_n$ its field
labels, and \texttt{C($f_1,\dots,f_n$)}, respectively, where
$f_1,\dots,f_n$ are the methods of type class \texttt{C}. In addition,
it replaces an export specification \verb|module M| by specifications
for all entities which are in scope with an unqualified name $x$ and a
qualified name \verb|M.|$x$. In order to distinguish exported type
constructors and type classes from exported functions, the former are
translated into the equivalent form \verb|T()| and \verb|C()|,
respectively. Note that the export specification \texttt{x} may export
a type constructor or type class \texttt{x} \emph{and} a global
function \texttt{x} at the same time.

The code of \texttt{expandSpecs} ensures that the unit, list, and
tuple types are exported from the Prelude even if its exported
entities are specified explicitly. On the other hand, the function
\texttt{expandModule} carefully excludes the identifiers of these
particular types in case a module's export list contains the
specification \texttt{module Prelude} so that these types are not
exported by any module other than the Prelude.
\begin{verbatim}

> expandSpecs :: Set ModuleIdent -> ModuleIdent -> TypeEnv -> FunEnv
>             -> Maybe ExportSpec -> Error ExportSpec
> expandSpecs ms m tEnv fEnv (Just (Exporting p es)) =
>   liftA (Exporting p . (es' ++) . concat)
>         (mapA (expandExport p (addToSet m ms) tEnv fEnv) es)
>   where es' = [exportType t | m == preludeMIdent,
>                               (tc,t) <- localBindings tEnv, isPrimTypeId tc]
> expandSpecs _ _ tEnv fEnv Nothing =
>   return (Exporting noPos (expandLocalModule tEnv fEnv))
>   where noPos = undefined

> expandExport :: Position -> Set ModuleIdent -> TypeEnv -> FunEnv -> Export
>              -> Error [Export]
> expandExport p _ tEnv fEnv (Export x) = expandThing p tEnv fEnv x
> expandExport p _ tEnv _ (ExportTypeWith tc xs) = expandTypeWith p tEnv tc xs
> expandExport p _ tEnv _ (ExportTypeAll tc) = expandTypeAll p tEnv tc
> expandExport p ms tEnv fEnv (ExportModule m)
>   | m `elemSet` ms = return (expandModule tEnv fEnv m)
>   | otherwise = errorAt p (moduleNotImported m)

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
>     [Var f' _] -> return (Export f' : fromMaybe [] tcExport)
>     [Constr _] -> maybe (errorAt p (exportDataConstr f)) return tcExport
>     _ -> errorAt p (ambiguousName f)

> expandTypeWith :: Position -> TypeEnv -> QualIdent -> [Ident]
>                -> Error [Export]
> expandTypeWith p tEnv tc xs =
>   do
>     (isType,tc',xs'') <- elements p tEnv tc
>     mapA_ (errorAt p . undefinedElement isType tc)
>           (filter (`notElem` xs'') xs')
>     return [ExportTypeWith tc' xs']
>   where xs' = nub xs

> expandTypeAll :: Position -> TypeEnv -> QualIdent -> Error [Export]
> expandTypeAll p tEnv tc =
>   do
>     (_,tc',xs) <- elements p tEnv tc
>     return [ExportTypeWith tc' xs]

> elements :: Position -> TypeEnv -> QualIdent -> Error (Bool,QualIdent,[Ident])
> elements p tEnv tc =
>   case qualLookupTopEnv tc tEnv of
>     [] -> errorAt p (undefinedEntity tc)
>     [Data tc xs] -> return (True,tc,xs)
>     [Alias tc] -> return (True,tc,[])
>     [Class cls fs] -> return (False,cls,fs)
>     _ -> errorAt p (ambiguousName tc)

> expandLocalModule :: TypeEnv -> FunEnv -> [Export]
> expandLocalModule tEnv fEnv =
>   [exportType t | (_,t) <- localBindings tEnv] ++
>   [Export f' | (_,Var f' _) <- localBindings fEnv]

> expandModule :: TypeEnv -> FunEnv -> ModuleIdent -> [Export]
> expandModule tEnv fEnv m =
>   [exportType (restrict xs t) | (tc,t) <- moduleBindings m tEnv,
>                                 not (isPrimTypeId tc)] ++
>   [Export f | Var f _ <- vs]
>   where vs = map snd (moduleBindings m fEnv)
>         xs = map origName vs
>         restrict xs' (Data tc xs) =
>           Data tc (filter ((`elem` xs') . qualifyLike tc) xs)
>         restrict _ (Alias tc) = Alias tc
>         restrict xs (Class cls fs) =
>           Class cls (filter ((`elem` xs) . qualifyLike cls) fs)

> exportType :: TypeKind -> Export
> exportType (Data tc xs) = ExportTypeWith tc xs
> exportType (Alias tc) = ExportTypeWith tc []
> exportType (Class cls fs) = ExportTypeWith cls fs

\end{verbatim}
For compatibility with Haskell, we allow exporting field labels and
type class methods but not constructors individually as well as
together with their types and classes, respectively. Thus, given the
declaration
\begin{verbatim}
  data T a = C{ l::a }
\end{verbatim}
the export lists \texttt{(T(C,l))} and \texttt{(T(C),l)} are
equivalent and both export the constructor \texttt{C} and the field
label \texttt{l} together with the type \texttt{T}. However, it is
also possible to export the label \texttt{l} without exporting its
type \texttt{T}. In this case, the label is exported just like a
top-level function (namely the implicit record selection function
corresponding to the label). In order to avoid ambiguities in the
interface, we convert an individual export of a label $l$ into the
form $T(l)$ whenever its type $T$ occurs in the export list as well.
\begin{verbatim}

> canonExports :: TypeEnv -> ExportSpec -> ExportSpec
> canonExports tEnv (Exporting p es) =
>   Exporting p (map (canonExport (canonElements tEnv es)) es)

> canonExport :: FM QualIdent Export -> Export -> Export
> canonExport xs (Export x) = fromMaybe (Export x) (lookupFM x xs)
> canonExport _ (ExportTypeWith tc xs) = ExportTypeWith tc xs

> canonElements :: TypeEnv -> [Export] -> FM QualIdent Export
> canonElements tEnv es = foldr bindElements zeroFM (allEntities tEnv)
>   where tcs = [tc | ExportTypeWith tc _ <- es]
>         bindElements (Data tc xs) ys
>           | tc `elem` tcs = foldr (bindElement tc) ys xs
>           | otherwise = ys
>         bindElements (Alias _) ys = ys
>         bindElements (Class cls fs) ys
>           | cls `elem` tcs = foldr (bindElement cls) ys fs
>           | otherwise = ys
>         bindElement tc x = addToFM (qualifyLike tc x) (ExportTypeWith tc [x])

\end{verbatim}
The expanded list of exported entities may contain duplicates. These
are removed by the function \texttt{nubExports}. In particular, this
function removes any field labels and type class methods from the list
of exported values which are also exported along with their types and
classes, respectively.
\begin{verbatim}

> nubExports :: ExportSpec -> ExportSpec
> nubExports (Exporting p es) = Exporting p $
>   [ExportTypeWith tc xs | (tc,xs) <- toListFM (foldr addType zeroFM es)] ++
>   [Export f | f <- toListSet (foldr addValue zeroSet es)]

> addType :: Export -> FM QualIdent [Ident] -> FM QualIdent [Ident]
> addType (Export _) tcs = tcs
> addType (ExportTypeWith tc xs) tcs =
>   addToFM tc (xs `union` fromMaybe [] (lookupFM tc tcs)) tcs

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
>   name c ++ " is not a constructor or label of type " ++ qualName tc
> undefinedElement False cls f =
>   name f ++ " is not a method of type class " ++ qualName cls

\end{verbatim}
