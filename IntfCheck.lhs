% -*- LaTeX -*-
% $Id: IntfCheck.lhs 1984 2006-10-27 13:34:07Z wlux $
%
% Copyright (c) 2000-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{IntfCheck.lhs}
\section{Interface Consistency Checks}
Interface files include declarations of all entities that are exported
by the module, but defined in another module. Since these declarations
can become inconsistent if client modules are not recompiled properly,
the compiler checks that all imported declarations in an interface
agree with their original definitions.

One may ask why we include imported declarations at all, if the
compiler always has to compare those declarations with the original
definitions. The main reason for this is that it helps to avoid
unnecessary recompilations of client modules. As an example, consider
the three modules
\begin{verbatim}
  module A where { data T = C }
  module B(T(..)) where { import A }
  module C where { import B; f = C }
\end{verbatim}
where module \texttt{B} could be considered as a public interface of
module \texttt{A}, which restricts access to type \texttt{A.T} and its
constructor \texttt{C}. The client module \texttt{C} imports this type
via the public interface \texttt{B}. If now module \texttt{A} is
changed by adding a definition of a new global function
\begin{verbatim}
  module A where { data T = C; f = C }
\end{verbatim}
module \texttt{B} must be recompiled because \texttt{A}'s interface is
changed. On the other hand, module \texttt{C} need not be recompiled
because the change in \texttt{A} does not affect \texttt{B}'s
interface. By including the declaration of type \texttt{A.T} in
\texttt{B}'s interface, the compiler can trivially check that
\texttt{B}'s interface remains unchanged and therefore the client
module \texttt{C} is not recompiled.

Another reason for including imported declarations in interfaces is
that the compiler in principle could avoid loading interfaces of
modules that are imported only indirectly, which would save processing
time and allow distributing binary packages of a library with a public
interface module only. However, this has not been implemented yet.
\begin{verbatim}

> module IntfCheck(intfCheck) where
> import Base
> import Error
> import Maybe
> import Monad
> import TopEnv
> import TypeTrans

> intfCheck :: ModuleIdent -> PEnv -> TCEnv -> ValueEnv -> [IDecl] -> Error ()
> intfCheck m pEnv tcEnv tyEnv = mapE_ (checkImport m pEnv tcEnv tyEnv)

> checkImport :: ModuleIdent -> PEnv -> TCEnv -> ValueEnv -> IDecl -> Error ()
> checkImport _ pEnv _ _ (IInfixDecl p fix pr op) =
>   checkPrecInfo checkPrec pEnv p op
>   where checkPrec (PrecInfo op' (OpPrec fix' pr')) =
>           op == op' && fix == fix' && pr == pr'
> checkImport _ _ tcEnv _ (HidingDataDecl p tc tvs) =
>   checkTypeInfo "hidden data type" checkData tcEnv p tc
>   where checkData (DataType tc' n' _)
>           | tc == tc' && length tvs == n' = Just (return ())
>         checkData (RenamingType tc' n' _)
>           | tc == tc' && length tvs == n' = Just (return ())
>         checkData _ = Nothing
> checkImport m _ tcEnv tyEnv (IDataDecl p tc tvs cs) =
>   checkTypeInfo "data type" checkData tcEnv p tc
>   where checkData (DataType tc' n' cs')
>           | tc == tc' && length tvs == n' &&
>             (null cs || length cs == length cs') &&
>             and (zipWith isVisible cs cs') =
>               Just (mapM_ (checkConstrImport m tyEnv tc tvs) (catMaybes cs))
>         checkData (RenamingType tc' n' _)
>           | tc == tc' && length tvs == n' && null cs = Just (return ())
>         checkData _ = Nothing
>         isVisible (Just c) (Just c') = constr c == c'
>         isVisible (Just _) Nothing = False
>         isVisible Nothing _ = True
> checkImport m _ tcEnv tyEnv (INewtypeDecl p tc tvs nc) =
>   checkTypeInfo "newtype" checkNewtype tcEnv p tc
>   where checkNewtype (RenamingType tc' n' nc')
>           | tc == tc' && length tvs == n' && nconstr nc == nc' =
>               Just (checkNewConstrImport m tyEnv tc tvs nc)
>         checkNewtype _ = Nothing
> checkImport m _ tcEnv _ (ITypeDecl p tc tvs ty) =
>   checkTypeInfo "synonym type" checkType tcEnv p tc
>   where checkType (AliasType tc' n' ty')
>           | tc == tc' && length tvs == n' && toType m tvs ty == ty' =
>               Just (return ())
>         checkType _ = Nothing
> checkImport m _ tcEnv _ (HidingClassDecl p cls tv) =
>   checkTypeInfo "hidden type class" checkClass tcEnv p cls
>   where checkClass (TypeClass cls') | cls == cls' = Just (return ())
>         checkClass _ = Nothing
> checkImport m _ tcEnv _ (IClassDecl p cls tv) =
>   checkTypeInfo "type class" checkClass tcEnv p cls
>   where checkClass (TypeClass cls') | cls == cls' = Just (return ())
>         checkClass _ = Nothing
> checkImport m _ _ _ (IInstanceDecl _ _ _) = return ()
> checkImport m _ _ tyEnv (IFunctionDecl p f ty) =
>   checkValueInfo "function" checkFun tyEnv p f
>   where checkFun (Value f' (ForAll _ ty')) =
>           f == f' && toQualType m [] ty == ty'
>         checkFun _ = False

> checkConstrImport :: ModuleIdent -> ValueEnv -> QualIdent -> [Ident]
>                   -> ConstrDecl -> Error ()
> checkConstrImport m tyEnv tc tvs (ConstrDecl p evs c tys) =
>   checkValueInfo "data constructor" checkConstr tyEnv p qc
>   where qc = qualifyLike tc c
>         checkConstr (DataConstructor c' (ForAll n' (QualType _ ty'))) =
>           qc == c' && length (tvs ++ evs) == n' &&
>           toTypes m tvs tys == arrowArgs ty'
>         checkConstr _ = False
> checkConstrImport m tyEnv tc tvs (ConOpDecl p evs ty1 op ty2) =
>   checkValueInfo "data constructor" checkConstr tyEnv p qc
>   where qc = qualifyLike tc op
>         checkConstr (DataConstructor c' (ForAll n' (QualType _ ty'))) =
>           qc == c' && length (tvs ++ evs) == n' &&
>           toTypes m tvs [ty1,ty2] == arrowArgs ty'
>         checkConstr _ = False

> checkNewConstrImport :: ModuleIdent -> ValueEnv -> QualIdent -> [Ident]
>                      -> NewConstrDecl -> Error ()
> checkNewConstrImport m tyEnv tc tvs (NewConstrDecl p c ty) =
>   checkValueInfo "newtype constructor" checkNewConstr tyEnv p qc
>   where qc = qualifyLike tc c
>         checkNewConstr (NewtypeConstructor c' (ForAll n' (QualType _ ty'))) =
>           qc == c' && length tvs == n' &&
>           toType m tvs ty == head (arrowArgs ty')
>         checkNewConstr _ = False

> checkPrecInfo :: (PrecInfo -> Bool) -> PEnv -> Position
>               -> QualIdent -> Error ()
> checkPrecInfo check pEnv p op = checkImported checkInfo op
>   where checkInfo m op' =
>           case qualLookupTopEnv op pEnv of
>             [] -> errorAt p (noPrecedence m op')
>             [pi] ->
>               unless (check pi)
>                      (errorAt p (importConflict "precedence" m op'))
>             _ -> internalError "checkPrecInfo"

> checkTypeInfo :: String -> (TypeInfo -> Maybe (Error ())) -> TCEnv -> Position
>               -> QualIdent -> Error ()
> checkTypeInfo what check tcEnv p tc = checkImported checkInfo tc
>   where checkInfo m tc' =
>           case qualLookupTopEnv tc tcEnv of
>             [] -> errorAt p (notExported what m tc')
>             [ti] ->
>               fromMaybe (errorAt p (importConflict what m tc')) (check ti)
>             _ -> internalError "checkTypeInfo"

> checkValueInfo :: String -> (ValueInfo -> Bool) -> ValueEnv -> Position
>                -> QualIdent -> Error ()
> checkValueInfo what check tyEnv p x = checkImported checkInfo x
>   where checkInfo m x' =
>           case qualLookupTopEnv x tyEnv of
>             [] -> errorAt p (notExported what m x')
>             [vi] -> unless (check vi) (errorAt p (importConflict what m x'))
>             _ -> internalError "checkValueInfo"

> checkImported :: (ModuleIdent -> Ident -> Error ()) -> QualIdent -> Error ()
> checkImported f x =
>   case splitQualIdent x of
>     (Just m,x') -> f m x'
>     (Nothing,_) -> return ()

\end{verbatim}
Error messages.
\begin{verbatim}

> notExported :: String -> ModuleIdent -> Ident -> String
> notExported what m x =
>   "Inconsistent module interfaces\n" ++
>   "Module " ++ moduleName m ++ " does not export " ++ what ++ " " ++ name x

> noPrecedence :: ModuleIdent -> Ident -> String
> noPrecedence m x =
>   "Inconsistent module interfaces\n" ++
>   "Module " ++ moduleName m ++ " does not define a precedence for " ++ name x

> importConflict :: String -> ModuleIdent -> Ident -> String
> importConflict what m x =
>   "Inconsistent module interfaces\n" ++
>   "Declaration of " ++ what ++ " " ++ name x ++
>   " does not match its definition in module " ++ moduleName m

\end{verbatim}
