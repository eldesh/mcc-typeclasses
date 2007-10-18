% -*- LaTeX -*-
% $Id: IntfCheck.lhs 2517 2007-10-18 14:23:42Z wlux $
%
% Copyright (c) 2000-2007, Wolfgang Lux
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
> import Curry
> import CurryUtils
> import Env
> import Error
> import InstInfo
> import Kinds
> import KindTrans
> import Maybe
> import Monad
> import PrecInfo
> import TopEnv
> import Types
> import TypeInfo
> import TypeTrans
> import ValueInfo

> intfCheck :: ModuleIdent -> PEnv -> TCEnv -> InstEnv -> ValueEnv -> [IDecl]
>           -> Error ()
> intfCheck m pEnv tcEnv iEnv tyEnv =
>   mapE_ (checkImport m pEnv tcEnv iEnv tyEnv)

> checkImport :: ModuleIdent -> PEnv -> TCEnv -> InstEnv -> ValueEnv -> IDecl
>             -> Error ()
> checkImport _ pEnv _ _ _ (IInfixDecl p fix pr op) =
>   checkPrecInfo checkPrec pEnv p op
>   where checkPrec (PrecInfo op' (OpPrec fix' pr')) =
>           op == op' && fix == fix' && pr == pr'
> checkImport _ _ tcEnv _ _ (HidingDataDecl p tc k tvs) =
>   checkTypeInfo "hidden data type" checkData tcEnv p tc
>   where checkData (DataType tc' k' _)
>           | tc == tc' && maybe (simpleKind (length tvs)) toKind k == k' =
>               Just (return ())
>         checkData (RenamingType tc' k' _)
>           | tc == tc' && maybe (simpleKind (length tvs)) toKind k == k' =
>               Just (return ())
>         checkData _ = Nothing
> checkImport m _ tcEnv _ tyEnv (IDataDecl p cx tc k tvs cs _) =
>   checkTypeInfo "data type" checkData tcEnv p tc
>   where checkData (DataType tc' k' cs')
>           | tc == tc' && maybe (simpleKind (length tvs)) toKind k == k' &&
>             (null cs || map constr cs == cs') =
>               Just (mapM_ (checkConstrImport m tyEnv cx tc tvs) cs)
>         checkData (RenamingType tc' k' _)
>           | tc == tc' && maybe (simpleKind (length tvs)) toKind k == k' &&
>             null cs =
>               Just (return ())
>         checkData _ = Nothing
> checkImport m _ tcEnv _ tyEnv (INewtypeDecl p cx tc k tvs nc) =
>   checkTypeInfo "newtype" checkNewtype tcEnv p tc
>   where checkNewtype (RenamingType tc' k' nc')
>           | tc == tc' && maybe (simpleKind (length tvs)) toKind k == k' &&
>             nconstr nc == nc' =
>               Just (checkNewConstrImport m tyEnv cx tc tvs nc)
>         checkNewtype _ = Nothing
> checkImport m _ tcEnv _ _ (ITypeDecl p tc k tvs ty) =
>   checkTypeInfo "synonym type" checkType tcEnv p tc
>   where checkType (AliasType tc' n' k' ty')
>           | tc == tc' && maybe (simpleKind (length tvs)) toKind k == k' &&
>             length tvs == n' && toType m tvs ty == ty' =
>               Just (return ())
>         checkType _ = Nothing
> checkImport m _ tcEnv _ _ (HidingClassDecl p cx cls k tv) =
>   checkTypeInfo "hidden type class" checkClass tcEnv p cls
>   where checkClass (TypeClass cls' k' clss' _)
>           | cls == cls' && maybe KindStar toKind k == k' &&
>             [qualQualify m cls | ClassAssert cls _ <- cx] == clss' =
>               Just (return ())
>         checkClass _ = Nothing
> checkImport m _ tcEnv _ tyEnv (IClassDecl p cx cls k tv ds) =
>   checkTypeInfo "type class" checkClass tcEnv p cls
>   where checkClass (TypeClass cls' k' clss' fs')
>           | cls == cls' && maybe KindStar toKind k == k' &&
>             [qualQualify m cls | ClassAssert cls _ <- cx] == clss' &&
>             length ds == length fs' &&
>             and (zipWith (isVisible imethod) ds fs') =
>               Just (mapM_ (checkMethodImport m tyEnv cls tv) (catMaybes ds))
>         checkClass _ = Nothing
> checkImport m _ _ iEnv _ (IInstanceDecl p cx cls ty m') =
>   checkInstInfo checkContext iEnv p (qualQualify m cls) tc m'
>   where QualType cx' ty' = toQualType m (QualTypeExpr cx ty)
>         tc = rootOfType ty'
>         checkContext cx'' = cx' == cx''
> checkImport m _ _ _ tyEnv (IFunctionDecl p f n ty) =
>   checkValueInfo "function" checkFun tyEnv p f
>   where checkFun (Value f' n' (ForAll _ ty')) =
>           f == f' && maybe True (toInteger n' ==) n && toQualType m ty == ty'
>         checkFun _ = False

> checkConstrImport :: ModuleIdent -> ValueEnv -> [ClassAssert] -> QualIdent
>                   -> [Ident] -> ConstrDecl -> Error ()
> checkConstrImport m tyEnv cxL tc tvs (ConstrDecl p evs cxR c tys) =
>   checkValueInfo "data constructor" checkConstr tyEnv p qc
>   where qc = qualifyLike tc c
>         checkConstr (DataConstructor c' _ ci' (ForAll n' ty')) =
>           qc == c' && length (tvs ++ evs) == n' &&
>           toConstrType m cxL tc tvs cxR tys == (ci',ty')
>         checkConstr _ = False
> checkConstrImport m tyEnv cxL tc tvs (ConOpDecl p evs cxR ty1 op ty2) =
>   checkValueInfo "data constructor" checkConstr tyEnv p qc
>   where qc = qualifyLike tc op
>         checkConstr (DataConstructor c' _ ci' (ForAll n' ty')) =
>           qc == c' && length (tvs ++ evs) == n' &&
>           toConstrType m cxL tc tvs cxR [ty1,ty2] == (ci',ty')
>         checkConstr _ = False

> checkNewConstrImport :: ModuleIdent -> ValueEnv -> [ClassAssert] -> QualIdent
>                      -> [Ident] -> NewConstrDecl -> Error ()
> checkNewConstrImport m tyEnv cx tc tvs (NewConstrDecl p c ty) =
>   checkValueInfo "newtype constructor" checkNewConstr tyEnv p qc
>   where qc = qualifyLike tc c
>         checkNewConstr (NewtypeConstructor c' (ForAll n' ty')) =
>           qc == c' && length tvs == n' &&
>           snd (toConstrType m cx tc tvs [] [ty]) == ty'
>         checkNewConstr _ = False

> checkMethodImport :: ModuleIdent -> ValueEnv -> QualIdent -> Ident
>                   -> IMethodDecl -> Error ()
> checkMethodImport m tyEnv cls tv (IMethodDecl p f ty) =
>   checkValueInfo "method" checkMethod tyEnv p qf
>   where qf = qualifyLike cls f
>         checkMethod (Value f' _ (ForAll _ ty')) =
>           qf == f' && toMethodType m cls tv ty == ty'
>         checkMethod _ = False

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

> checkInstInfo :: (Context -> Bool) -> InstEnv -> Position
>               -> QualIdent -> QualIdent -> Maybe ModuleIdent -> Error ()
> checkInstInfo checkContext iEnv p cls tc m =
>   checkImported checkInfo (maybe qualify qualifyWith m anonId)
>   where checkInfo m' _ =
>           case lookupEnv (CT cls tc) iEnv of
>             Just (m,cx)
>               | m /= m' -> errorAt p (noInstance m' cls tc)
>               | otherwise ->
>                   unless (checkContext cx)
>                          (errorAt p (instanceConflict m' cls tc))
>             Nothing -> errorAt p (noInstance m' cls tc)

> checkImported :: (ModuleIdent -> Ident -> Error ()) -> QualIdent -> Error ()
> checkImported f x =
>   case splitQualIdent x of
>     (Just m,x') -> f m x'
>     (Nothing,_) -> return ()

> isVisible :: (a -> Ident) -> Maybe a -> Maybe Ident -> Bool
> isVisible f (Just d) (Just x) = f d == x
> isVisible _ (Just _) Nothing = False
> isVisible _ Nothing _ = True

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

> noInstance :: ModuleIdent -> QualIdent -> QualIdent -> String
> noInstance m cls tc =
>   "Inconsistent module interfaces\n" ++
>   "Module " ++ moduleName m ++ " does not define an instance " ++
>   qualName cls ++ " " ++ qualName tc

> importConflict :: String -> ModuleIdent -> Ident -> String
> importConflict what m x =
>   "Inconsistent module interfaces\n" ++
>   "Declaration of " ++ what ++ " " ++ name x ++
>   " does not match its definition in module " ++ moduleName m

> instanceConflict :: ModuleIdent -> QualIdent -> QualIdent -> String
> instanceConflict m cls tc =
>   "Inconsistent module interfaces\n" ++
>   "Declaration of instance " ++ qualName cls ++ " " ++ qualName tc ++
>   " does not match its definition in module " ++ moduleName m

\end{verbatim}
