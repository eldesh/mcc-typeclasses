% -*- LaTeX -*-
% $Id: Imports.lhs 2815 2009-05-04 13:59:57Z wlux $
%
% Copyright (c) 2000-2008, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Imports.lhs}
\section{Importing Interfaces}
This module provides a few functions which can be used to import
interfaces into the current module.
\begin{verbatim}

> module Imports(importIdents,importInterface,importInterfaceIntf,
>                importUnifyData) where
> import Base
> import Curry
> import CurryUtils
> import Env
> import IdentInfo
> import InstInfo
> import Kinds
> import KindTrans
> import List
> import Maybe
> import Map
> import PrecInfo
> import PredefIdent
> import Set
> import TopEnv
> import Types
> import TypeInfo
> import TypeTrans
> import ValueInfo

\end{verbatim}
When an interface is imported into a module, the compiler must respect
the import specifications in the import declaration. If an import
specification is present, only those entities which are included in
the specification or not hidden by it, respectively, are added to the
global environments. If the qualified flag is present, only a
qualified import is performed. Otherwise, both a qualified and an
unqualified import are performed. Regardless of the type of import,
all instance declarations are always imported into the current module.
\begin{verbatim}

> importIdents :: ModuleIdent -> Bool -> Maybe ImportSpec
>              -> (TypeEnv,InstSet,FunEnv) -> Interface
>              -> (TypeEnv,InstSet,FunEnv)
> importIdents m q is (tEnv,iSet,vEnv) (Interface _ _ ds) =
>   (importEntities tidents m q ts (importMembers vs) ds tEnv,
>    importCTs ds iSet,
>    importEntities vidents m q vs id ds vEnv)
>   where ts = isVisible addType is
>         vs = isVisible addValue is

> importInterface :: ModuleIdent -> Bool -> Maybe ImportSpec
>                 -> (PEnv,TCEnv,InstEnv,ValueEnv) -> Interface
>                 -> (PEnv,TCEnv,InstEnv,ValueEnv)
> importInterface m q is (pEnv,tcEnv,iEnv,tyEnv) (Interface _ _ ds) =
>   (importEntities precs m q vs id ds pEnv,
>    importEntities types m q ts id ds tcEnv,
>    importInstances ds iEnv,
>    importEntities values m q vs id ds tyEnv)
>   where ts = isVisible addType is
>         vs = isVisible addValue is

> isVisible :: (Import -> Set Ident -> Set Ident) -> Maybe ImportSpec
>           -> Ident -> Bool
> isVisible add (Just (Importing _ xs)) = (`elemSet` foldr add zeroSet xs)
> isVisible add (Just (Hiding _ xs)) = (`notElemSet` foldr add zeroSet xs)
> isVisible _ Nothing = const True

> importEntities :: Entity a => (IDecl -> [a]) -> ModuleIdent -> Bool
>                -> (Ident -> Bool) -> (a -> a) -> [IDecl]
>                -> TopEnv a -> TopEnv a
> importEntities ents m q isVisible f ds env =
>   foldr (uncurry (importTopEnv q m)) env
>         [(x,f y) | y <- concatMap ents ds,
>                    let x = unqualify (origName y), isVisible x]

> importMembers :: (Ident -> Bool) -> TypeKind -> TypeKind
> importMembers isVisible (Data tc xs) = Data tc (filter isVisible xs)
> importMembers _ (Alias tc) = Alias tc
> importMembers isVisible (Class cls fs) = Class cls (filter isVisible fs)

> importMember :: (Ident -> Bool) -> Ident -> Maybe Ident
> importMember isVisible c
>   | isVisible c = Just c
>   | otherwise = Nothing

> importCTs :: [IDecl] -> InstSet -> InstSet
> importCTs ds iEnv = foldr addCT iEnv ds

> addCT :: IDecl -> InstSet -> InstSet
> addCT (IInstanceDecl _ _ cls ty _ _) = addToSet (CT cls (typeConstr ty))
> addCT _ = id

> importInstances :: [IDecl] -> InstEnv -> InstEnv
> importInstances ds iEnv = foldr bindInstance iEnv ds

> bindInstance :: IDecl -> InstEnv -> InstEnv
> bindInstance (IInstanceDecl _ cx cls ty (Just m) fs) =
>   bindEnv (CT cls (rootOfType ty')) (m,cx',fs')
>   where QualType cx' ty' = toQualType (QualTypeExpr cx ty)
>         fs' = [(f,fromInteger n) | (f,n) <- fs]
> bindInstance _ = id

\end{verbatim}
Importing an interface into another interface is somewhat simpler
because only a qualified import is necessary and there are no import
restrictions. Besides entities defined in the interface's module, we
must also import entities that are reexported from other modules
provided that the compiler did not load the respective interfaces.

Note that the first argument of \texttt{importInterfaceIntf} is the
list of names of the modules whose interfaces have been read by the
compiler. Obviously, this must include the current interface's module
name.
\begin{verbatim}

> importInterfaceIntf :: [ModuleIdent] -> (PEnv,TCEnv,InstEnv,ValueEnv)
>                     -> Interface -> (PEnv,TCEnv,InstEnv,ValueEnv)
> importInterfaceIntf ms (pEnv,tcEnv,iEnv,tyEnv) (Interface m is ds) =
>   (importEntitiesIntf precs m ds' pEnv,
>    importEntitiesIntf types m ds' tcEnv,
>    importInstances ds' iEnv,
>    importEntitiesIntf values m ds' tyEnv)
>   where ms' = m : [m | IImportDecl _ m <- is, m `notElem` ms]
>         ds' = map unhide (filter (importEntity . entity) ds)
>         importEntity = maybe True (`elem` ms') . fst . splitQualIdent

> importEntitiesIntf :: Entity a => (IDecl -> [a]) -> ModuleIdent -> [IDecl]
>                    -> TopEnv a -> TopEnv a
> importEntitiesIntf ents m ds env = foldr importEntity env (concatMap ents ds)
>   where importEntity x = qualImportTopEnv m (origName x) x

\end{verbatim}
The list of entities exported from a module is computed with the
following functions.
\begin{verbatim}

> precs :: IDecl -> [PrecInfo]
> precs (IInfixDecl _ fix p op) = [PrecInfo op (OpPrec fix p)]
> precs _ = []

> types :: IDecl -> [TypeInfo]
> types (IDataDecl _ _ tc k tvs cs _) =
>   [typeCon DataType tc k tvs (map constr cs)]
> types (INewtypeDecl _ _ tc k tvs nc _) =
>   [typeCon RenamingType tc k tvs (nconstr nc)]
> types (ITypeDecl _ tc k tvs ty) =
>   [typeCon (flip AliasType (length tvs)) tc k tvs (toType tvs ty)]
> types (IClassDecl _ cx cls k tv ds _) = [typeCls cx cls k tv (map clsMthd ds)]
> types _ = []

> typeCon :: (QualIdent -> Kind -> a) -> QualIdent -> Maybe KindExpr -> [Ident]
>         -> a
> typeCon f tc k tvs = f tc (maybe (simpleKind (length tvs)) toKind k)

> typeCls :: [ClassAssert] -> QualIdent -> Maybe KindExpr -> Ident -> MethodList
>         -> TypeInfo
> typeCls cx cls k tv fs =
>   TypeClass cls (maybe KindStar toKind k) [cls | TypePred cls _ <- cx'] fs
>   where QualType cx' _ = toQualType (QualTypeExpr cx (VariableType tv))

> clsMthd :: IMethodDecl -> (Ident,Int)
> clsMthd (IMethodDecl _ f n _) = (f,maybe 0 fromInteger n)

> values :: IDecl -> [ValueInfo]
> values (IDataDecl _ cx tc _ tvs cs xs) =
>   map (dataConstr cx tc tvs) (filter ((`notElem` xs) . constr) cs) ++
>   map (uncurry (fieldLabel cx tc tvs)) (nubBy sameLabel ls)
>   where ls = [(l,ty) | RecordDecl _ _ _ _ fs <- cs,
>                        FieldDecl _ ls ty <- fs, l <- ls, l `notElem` xs]
>         sameLabel (l1,_) (l2,_) = l1 == l2
> values (INewtypeDecl _ cx tc _ tvs nc xs) =
>   map (newConstr cx tc tvs) [nc | nconstr nc `notElem` xs] ++
>   case nc of
>     NewConstrDecl _ _ _ -> []
>     NewRecordDecl _ c l ty -> [fieldLabel cx tc tvs l ty | l `notElem` xs]
> values (IClassDecl _ _ cls _ tv ds fs') =
>   map (classMethod cls tv) (filter ((`notElem` fs') . imethod) ds)
> values (IFunctionDecl _ f n ty) = [Value f n' (typeScheme ty')]
>   where n' = maybe (arrowArity (unqualType ty')) fromInteger n
>         ty' = toQualType ty
> values _ = []

> dataConstr :: [ClassAssert] -> QualIdent -> [Ident] -> ConstrDecl -> ValueInfo
> dataConstr cxL tc tvs (ConstrDecl _ _ cxR c tys) =
>   con cxL tc tvs cxR c (zip (repeat anonId) tys)
> dataConstr cxL tc tvs (ConOpDecl _ _ cxR ty1 op ty2) =
>   con cxL tc tvs cxR op [(anonId,ty1),(anonId,ty2)]
> dataConstr cxL tc tvs (RecordDecl _ _ cxR c fs) =
>   con cxL tc tvs cxR c [(l,ty) | FieldDecl _ ls ty <- fs, l <- ls]

> con :: [ClassAssert] -> QualIdent -> [Ident] -> [ClassAssert] -> Ident
>     -> [(Ident,TypeExpr)] -> ValueInfo
> con cxL tc tvs cxR c tys =
>   DataConstructor (qualifyLike tc c) ls ci (typeScheme ty)
>   where (ci,ty) = toConstrType cxL tc tvs cxR tys'
>         (ls,tys') = unzip tys

> newConstr :: [ClassAssert] -> QualIdent -> [Ident] -> NewConstrDecl
>           -> ValueInfo
> newConstr cx tc tvs (NewConstrDecl _ c ty) = ncon cx tc tvs c anonId ty
> newConstr cx tc tvs (NewRecordDecl _ c l ty) = ncon cx tc tvs c l ty

> ncon :: [ClassAssert] -> QualIdent -> [Ident] -> Ident -> Ident -> TypeExpr
>      -> ValueInfo
> ncon cx tc tvs c l ty =
>   NewtypeConstructor (qualifyLike tc c) l (typeScheme ty')
>   where ty' = snd (toConstrType cx tc tvs [] [ty])

> fieldLabel :: [ClassAssert] -> QualIdent -> [Ident] -> Ident -> TypeExpr
>            -> ValueInfo
> fieldLabel cx tc tvs l ty =
>   Value (qualifyLike tc l) 1 (typeScheme (toQualType ty'))
>   where ty' = QualTypeExpr cx (ArrowType (constrType tc tvs) ty)

> classMethod :: QualIdent -> Ident -> IMethodDecl -> ValueInfo
> classMethod cls tv (IMethodDecl _ f _ ty) =
>   Value (qualifyLike cls f) 0 (typeScheme (toMethodType cls tv ty))

\end{verbatim}
After all modules have been imported, the compiler has to ensure that
all references to a data type use the same list of constructors and
all references to a type class use the same list of methods. Ditto for
all references to a field label.
\begin{verbatim}

> importUnifyData :: Entity a => TopEnv a -> TopEnv a
> importUnifyData tcEnv =
>   fmap (updWith (foldr (mergeData . snd) zeroFM (allImports tcEnv))) tcEnv
>   where updWith tcs t = fromMaybe t (lookupFM (origName t) tcs)
>         mergeData t tcs =
>           addToFM tc (maybe t (fromJust . merge t) (lookupFM tc tcs)) tcs
>           where tc = origName t

\end{verbatim}
Auxiliary functions:
\begin{verbatim}

> addType :: Import -> Set Ident -> Set Ident
> addType (Import _) tcs = tcs
> addType (ImportTypeWith tc _) tcs = addToSet tc tcs
> addType (ImportTypeAll _) _ = internalError "addType"

> addValue :: Import -> Set Ident -> Set Ident
> addValue (Import f) fs = addToSet f fs
> addValue (ImportTypeWith _ xs) fs = foldr addToSet fs xs
> addValue (ImportTypeAll _) _ = internalError "addValue"

> constrType :: QualIdent -> [Ident] -> TypeExpr
> constrType tc tvs =
>   foldl ApplyType (ConstructorType tc) (map VariableType tvs)

\end{verbatim}
