% -*- LaTeX -*-
% $Id: IntfCheck.lhs 2815 2009-05-04 13:59:57Z wlux $
%
% Copyright (c) 2000-2008, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{IntfCheck.lhs}
\section{Interface Consistency Checks}
Interface files include declarations of all entities that are exported
by the module but defined in another module. Since these declarations
can become inconsistent if client modules are not recompiled properly,
the compiler checks that all imported declarations in interfaces are
consistent and agree with their original definitions where they are
available.

The main rationale for this design decision is that it is sufficient
to read only the interfaces of the Prelude and those modules that are
imported explicitly by the compiled module if the definitions of all
exported entities are present in an interface. This makes
bootstrapping simpler for mutually recursive modules, in particular if
the mutual recursion also shows up in the interfaces. Furthermore, it
helps avoiding unnecessary recompilation of client modules. As an
example, consider the three modules
\begin{verbatim}
  module A where { data T = C }
  module B(T(..)) where { import A }
  module C where { import B; f = C }
\end{verbatim}
where module \texttt{B} could be considered the public interface of
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

When detecting a conflict between the definition of an imported
entity, say \texttt{A.x}, in the interfaces of modules \texttt{B} and
\texttt{C}, respectively, we have to distinguish whether the interface
of module \texttt{A} has been loaded as well or not. In the former
case, we can give an authoritative answer whether \texttt{A.x}'s
definition in \texttt{B} is wrong or whether the definition in
\texttt{C} is wrong. We can even detect if \texttt{A} does not export
\texttt{x} at all. In the latter case, we can not give an
authoritative answer which definition is wrong and therefore report an
error for both.
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
> import List
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
> intfCheck m pEnv tcEnv iEnv tyEnv ds =
>   mapE_ (checkImport pEnv tcEnv iEnv tyEnv)
>         (filter (isNothing . localIdent m . entity) ds)

> checkImport :: PEnv -> TCEnv -> InstEnv -> ValueEnv -> IDecl -> Error ()
> checkImport pEnv _ _ _ (IInfixDecl p fix pr op) =
>   checkPrecInfo checkPrec pEnv p op
>   where checkPrec (PrecInfo op' (OpPrec fix' pr')) =
>           op == op' && fix == fix' && pr == pr'
> checkImport _ tcEnv _ _ (HidingDataDecl p tc k tvs) =
>   checkTypeInfo "hidden data type" checkData tcEnv p tc
>   where checkData (DataType tc' k' _)
>           | tc == tc' && maybe (simpleKind (length tvs)) toKind k == k' =
>               Just (return ())
>         checkData (RenamingType tc' k' _)
>           | tc == tc' && maybe (simpleKind (length tvs)) toKind k == k' =
>               Just (return ())
>         checkData _ = Nothing
> checkImport _ tcEnv _ tyEnv (IDataDecl p cx tc k tvs cs _) =
>   checkTypeInfo "data type" checkData tcEnv p tc
>   where checkData (DataType tc' k' cs')
>           | tc == tc' && maybe (simpleKind (length tvs)) toKind k == k' &&
>             (null cs || map constr cs == cs') =
>               Just (mapM_ (checkConstrImport tyEnv cx tc tvs) cs)
>         checkData _ = Nothing
> checkImport _ tcEnv _ tyEnv (INewtypeDecl p cx tc k tvs nc _) =
>   checkTypeInfo "newtype" checkNewtype tcEnv p tc
>   where checkNewtype (RenamingType tc' k' nc')
>           | tc == tc' && maybe (simpleKind (length tvs)) toKind k == k' &&
>             nconstr nc == nc' =
>               Just (checkNewConstrImport tyEnv cx tc tvs nc)
>         checkNewtype _ = Nothing
> checkImport _ tcEnv _ _ (ITypeDecl p tc k tvs ty) =
>   checkTypeInfo "synonym type" checkType tcEnv p tc
>   where checkType (AliasType tc' n' k' ty')
>           | tc == tc' && maybe (simpleKind (length tvs)) toKind k == k' &&
>             length tvs == n' && toType tvs ty == ty' =
>               Just (return ())
>         checkType _ = Nothing
> checkImport _ tcEnv _ _ (HidingClassDecl p cx cls k tv) =
>   checkTypeInfo "hidden type class" checkClass tcEnv p cls
>   where checkClass (TypeClass cls' k' clss' _)
>           | cls == cls' && maybe KindStar toKind k == k' &&
>             [cls | ClassAssert cls _ <- cx] == clss' =
>               Just (return ())
>         checkClass _ = Nothing
> checkImport _ tcEnv _ tyEnv (IClassDecl p cx cls k tv ds _) =
>   checkTypeInfo "type class" checkClass tcEnv p cls
>   where checkClass (TypeClass cls' k' clss' fs')
>           | cls == cls' && maybe KindStar toKind k == k' &&
>             [cls | ClassAssert cls _ <- cx] == clss' &&
>             [(f,maybe 0 fromInteger n) | IMethodDecl _ f n _ <- ds] == fs' =
>               Just (mapM_ (checkMethodImport tyEnv cls tv) ds)
>         checkClass _ = Nothing
> checkImport _ _ iEnv _ (IInstanceDecl p cx cls ty m fs) =
>   checkInstInfo checkInst iEnv p cls tc m
>   where QualType cx' ty' = toQualType (QualTypeExpr cx ty)
>         tc = rootOfType ty'
>         checkInst cx'' fs' =
>           cx' == cx'' && sort fs == sort [(f,toInteger n) | (f,n) <- fs']
> checkImport _ _ _ tyEnv (IFunctionDecl p f n ty) =
>   checkValueInfo "function" checkFun tyEnv p f
>   where checkFun (Value f' n' (ForAll _ ty')) =
>           f == f' && maybe True (toInteger n' ==) n && toQualType ty == ty'
>         checkFun _ = False

> checkConstrImport :: ValueEnv -> [ClassAssert] -> QualIdent -> [Ident]
>                   -> ConstrDecl -> Error ()
> checkConstrImport tyEnv cxL tc tvs (ConstrDecl p evs cxR c tys) =
>   checkValueInfo "data constructor" checkConstr tyEnv p qc
>   where qc = qualifyLike tc c
>         checkConstr (DataConstructor c' _ ci' (ForAll n' ty')) =
>           qc == c' && length (tvs ++ evs) == n' &&
>           toConstrType cxL tc tvs cxR tys == (ci',ty')
>         checkConstr _ = False
> checkConstrImport tyEnv cxL tc tvs (ConOpDecl p evs cxR ty1 op ty2) =
>   checkValueInfo "data constructor" checkConstr tyEnv p qc
>   where qc = qualifyLike tc op
>         checkConstr (DataConstructor c' _ ci' (ForAll n' ty')) =
>           qc == c' && length (tvs ++ evs) == n' &&
>           toConstrType cxL tc tvs cxR [ty1,ty2] == (ci',ty')
>         checkConstr _ = False
> checkConstrImport tyEnv cxL tc tvs (RecordDecl p evs cxR c fs) =
>   checkValueInfo "data constructor" checkConstr tyEnv p qc
>   where qc = qualifyLike tc c
>         (ls,tys) = unzip [(l,ty) | FieldDecl _ ls ty <- fs, l <- ls]
>         checkConstr (DataConstructor c' ls' ci' (ForAll n' ty')) =
>           qc == c' && length (tvs ++ evs) == n' && ls == ls' &&
>           toConstrType cxL tc tvs cxR tys == (ci',ty')
>         checkConstr _ = False

> checkNewConstrImport :: ValueEnv -> [ClassAssert] -> QualIdent -> [Ident]
>                      -> NewConstrDecl -> Error ()
> checkNewConstrImport tyEnv cx tc tvs (NewConstrDecl p c ty) =
>   checkValueInfo "newtype constructor" checkNewConstr tyEnv p qc
>   where qc = qualifyLike tc c
>         checkNewConstr (NewtypeConstructor c' _ (ForAll n' ty')) =
>           qc == c' && length tvs == n' &&
>           snd (toConstrType cx tc tvs [] [ty]) == ty'
>         checkNewConstr _ = False
> checkNewConstrImport tyEnv cx tc tvs (NewRecordDecl p c l ty) =
>   checkValueInfo "newtype constructor" checkNewConstr tyEnv p qc
>   where qc = qualifyLike tc c
>         checkNewConstr (NewtypeConstructor c' l' (ForAll n' ty')) =
>           qc == c' && length tvs == n' && l == l' &&
>           snd (toConstrType cx tc tvs [] [ty]) == ty'
>         checkNewConstr _ = False

> checkMethodImport :: ValueEnv -> QualIdent -> Ident -> IMethodDecl -> Error ()
> checkMethodImport tyEnv cls tv (IMethodDecl p f _ ty) =
>   checkValueInfo "method" checkMethod tyEnv p qf
>   where qf = qualifyLike cls f
>         checkMethod (Value f' _ (ForAll _ ty')) =
>           qf == f' && toMethodType cls tv ty == ty'
>         checkMethod _ = False

> checkPrecInfo :: (PrecInfo -> Bool) -> PEnv -> Position
>               -> QualIdent -> Error ()
> checkPrecInfo check pEnv p op = checkImported checkInfo op
>   where what = "precedence"
>         checkInfo m op' =
>           case qualLookupTopEnv op pEnv of
>             [] -> errorAt p (noPrecedence m op')
>             [pi] -> unless (check pi) (errorAt p (importConflict what m op'))
>             _ -> errorAt p (inconsistentImports what op)

> checkTypeInfo :: String -> (TypeInfo -> Maybe (Error ())) -> TCEnv -> Position
>               -> QualIdent -> Error ()
> checkTypeInfo what check tcEnv p tc = checkImported checkInfo tc
>   where checkInfo m tc' =
>           case qualLookupTopEnv tc tcEnv of
>             [] -> errorAt p (notExported what m tc')
>             [ti] ->
>               fromMaybe (errorAt p (importConflict what m tc')) (check ti)
>             _ -> errorAt p (inconsistentImports what tc)

> checkValueInfo :: String -> (ValueInfo -> Bool) -> ValueEnv -> Position
>                -> QualIdent -> Error ()
> checkValueInfo what check tyEnv p x = checkImported checkInfo x
>   where checkInfo m x' =
>           case qualLookupTopEnv x tyEnv of
>             [] -> errorAt p (notExported what m x')
>             [vi] -> unless (check vi) (errorAt p (importConflict what m x'))
>             _ -> errorAt p (inconsistentImports what x)

> checkInstInfo :: (Context -> MethodList -> Bool) -> InstEnv -> Position
>               -> QualIdent -> QualIdent -> Maybe ModuleIdent -> Error ()
> checkInstInfo checkInst iEnv p cls tc m =
>   checkImported checkInfo (maybe qualify qualifyWith m anonId)
>   where checkInfo m' _ =
>           case lookupEnv (CT cls tc) iEnv of
>             Just (m,cx,fs)
>               | m /= m' -> errorAt p (noInstance m' cls tc)
>               | otherwise ->
>                   unless (checkInst cx fs)
>                          (errorAt p (instanceConflict m' cls tc))
>             Nothing -> errorAt p (noInstance m' cls tc)

> checkImported :: (ModuleIdent -> Ident -> Error ()) -> QualIdent -> Error ()
> checkImported f x = uncurry (f . fromJust) (splitQualIdent x)

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

> inconsistentImports :: String -> QualIdent -> String
> inconsistentImports what x =
>   "Inconsistent module interfaces\n" ++
>   "Found inconsistent declarations for imported " ++ what ++ " " ++ qualName x

\end{verbatim}
