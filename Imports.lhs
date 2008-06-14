% -*- LaTeX -*-
% $Id: Imports.lhs 2723 2008-06-14 15:56:40Z wlux $
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

> type I a = (Ident,a)

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

> importEntities :: Entity a
>                => (IDecl -> [I a] -> [I a])
>                -> ModuleIdent -> Bool -> (Ident -> Bool) -> (a -> a)
>                -> [IDecl] -> TopEnv a -> TopEnv a
> importEntities bind m q isVisible f ds env =
>   foldr (uncurry (importTopEnv q m)) env
>         [(x,f y) | (x,y) <- foldr bind [] ds, isVisible x]

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
> addCT (IInstanceDecl _ _ cls ty _) = addToSet (CT cls (typeConstr ty))
> addCT _ = id

> importInstances :: [IDecl] -> InstEnv -> InstEnv
> importInstances ds iEnv = foldr bindInstance iEnv ds

> bindInstance :: IDecl -> InstEnv -> InstEnv
> bindInstance (IInstanceDecl _ cx cls ty (Just m)) =
>   bindEnv (CT cls (rootOfType ty')) (m,cx')
>   where QualType cx' ty' = toQualType (QualTypeExpr cx ty)
> bindInstance _ = id

\end{verbatim}
Importing an interface into another interface is somewhat simpler
because all entities are imported into the environments. In addition,
only a qualified import is necessary. Only those entities that are
actually defined in the module are imported. Since the compiler
imports all used interfaces into other interfaces, entities defined in
one module and reexported by another module are made available by
their defining modules. Furthermore, ignoring reexported entities
avoids a problem with the fact that the unqualified name of an entity
defined in an interface may be ambiguous if hidden data type and class
declarations are taken into account. For instance, for the interface
\begin{verbatim}
  module M where {
    import N;
    hiding data N.T;
    type T a = (a,N.T)
  }
\end{verbatim}
the unqualified type identifier \verb|T| would be ambiguous if
\verb|N.T| were not ignored. Instance declarations are always included
(by returning \verb|qualify anonId| from \verb|entity|) because there
is no means to distinguish instances defined in a module from
instances imported from another module.
\begin{verbatim}

> importInterfaceIntf :: (PEnv,TCEnv,InstEnv,ValueEnv) -> Interface
>                     -> (PEnv,TCEnv,InstEnv,ValueEnv)
> importInterfaceIntf (pEnv,tcEnv,iEnv,tyEnv) (Interface m _ ds) =
>   (importEntitiesIntf precs m ds' pEnv,
>    importEntitiesIntf types m ds' tcEnv,
>    importInstances ds' iEnv,
>    importEntitiesIntf values m ds' tyEnv)
>   where ds' = map unhide (filter (isJust . localIdent m . entity) ds)

> unhide :: IDecl -> IDecl
> unhide (IInfixDecl p fix pr op) = IInfixDecl p fix pr op
> unhide (HidingDataDecl p tc k tvs) = IDataDecl p [] tc k tvs [] []
> unhide (IDataDecl p cx tc k tvs cs _) = IDataDecl p cx tc k tvs cs []
> unhide (INewtypeDecl p cx tc k tvs nc _) = INewtypeDecl p cx tc k tvs nc []
> unhide (ITypeDecl p tc k tvs ty) = ITypeDecl p tc k tvs ty
> unhide (HidingClassDecl p cx cls k tv) = IClassDecl p cx cls k tv [] []
> unhide (IClassDecl p cx cls k tv ds _) = IClassDecl p cx cls k tv ds []
> unhide (IInstanceDecl p cx cls ty m) = IInstanceDecl p cx cls ty m
> unhide (IFunctionDecl p f n ty) = IFunctionDecl p f n ty

> importEntitiesIntf :: Entity a
>                    => (IDecl -> [I a] -> [I a])
>                    -> ModuleIdent -> [IDecl] -> TopEnv a -> TopEnv a
> importEntitiesIntf bind m ds env =
>   foldr (uncurry (qualImportTopEnv m)) env (foldr bind [] ds)

\end{verbatim}
The list of entities exported from a module is computed with the
following functions.
\begin{verbatim}

> tidents :: IDecl -> [I TypeKind] -> [I TypeKind]
> tidents (IDataDecl _ _ tc _ _ cs xs') =
>   qual tc (Data tc (filter (`notElem` xs') xs))
>   where xs = map constr cs ++ nub (concatMap labels cs)
> tidents (INewtypeDecl _ _ tc _ _ nc xs') =
>   qual tc (Data tc (filter (`notElem` xs') xs))
>   where xs = nconstr nc : nlabel nc
> tidents (ITypeDecl _ tc _ _ _) = qual tc (Alias tc)
> tidents (IClassDecl _ _ cls _ _ ds fs') =
>   qual cls (Class cls (filter (`notElem` fs') (map imethod ds)))
> tidents _ = id

> vidents :: IDecl -> [I ValueKind] -> [I ValueKind]
> vidents (IDataDecl _ _ tc _ _ cs xs) =
>   cidents tc xs (map constr cs) .
>   lidents tc xs [(l,constrs cs l) | l <- nub (concatMap labels cs)]
>   where constrs cs l = [constr c | c <- cs, l `elem` labels c]
> vidents (INewtypeDecl _ _ tc _ _ nc xs) =
>   cidents tc xs [nconstr nc] .
>   case nc of
>     NewConstrDecl _ _ _ -> id
>     NewRecordDecl _ c l _ -> lidents tc xs [(l,[c])]
> vidents (IClassDecl _ _ cls _ _ ds fs) = midents cls fs (map imethod ds)
> vidents (IFunctionDecl _ f _ _) = qual f (Var f [])
> vidents _ = id

> precs :: IDecl -> [I PrecInfo] -> [I PrecInfo]
> precs (IInfixDecl _ fix p op) = qual op (PrecInfo op (OpPrec fix p))
> precs _ = id

> types :: IDecl -> [I TypeInfo] -> [I TypeInfo]
> types (IDataDecl _ _ tc k tvs cs _) =
>   qual tc (typeCon DataType tc k tvs (map constr cs))
> types (INewtypeDecl _ _ tc k tvs nc _) =
>   qual tc (typeCon RenamingType tc k tvs (nconstr nc))
> types (ITypeDecl _ tc k tvs ty) =
>   qual tc (typeCon (flip AliasType (length tvs)) tc k tvs (toType tvs ty))
> types (IClassDecl _ cx cls k tv ds _) =
>   qual cls (typeCls cx cls k tv (map imethod ds))
> types _ = id

> values :: IDecl -> [I ValueInfo] -> [I ValueInfo]
> values (IDataDecl _ cx tc _ tvs cs xs) =
>   (map (dataConstr cx tc tvs) (filter ((`notElem` xs) . constr) cs) ++) .
>   (map (uncurry (fieldLabel cx tc tvs)) (nubBy sameLabel ls) ++)
>   where ls = [(l,ty) | RecordDecl _ _ _ _ fs <- cs,
>                        FieldDecl _ ls ty <- fs, l <- ls, l `notElem` xs]
>         sameLabel (l1,_) (l2,_) = l1 == l2
> values (INewtypeDecl _ cx tc _ tvs nc xs) =
>   (map (newConstr cx tc tvs) [nc | nconstr nc `notElem` xs] ++) .
>   case nc of
>     NewConstrDecl _ _ _ -> id
>     NewRecordDecl _ c l ty
>       | l `notElem` xs -> (fieldLabel cx tc tvs l ty :)
>       | otherwise -> id
> values (IClassDecl _ _ cls _ tv ds fs') =
>   (map (classMethod cls tv) (filter ((`notElem` fs') . imethod) ds) ++)
> values (IFunctionDecl _ f n ty) = qual f (Value f n' (typeScheme ty'))
>   where n' = maybe (arrowArity (unqualType ty')) fromInteger n
>         ty' = toQualType ty
> values _ = id

> dataConstr :: [ClassAssert] -> QualIdent -> [Ident] -> ConstrDecl
>            -> I ValueInfo
> dataConstr cxL tc tvs (ConstrDecl _ _ cxR c tys) =
>   con cxL tc tvs cxR c (zip (repeat anonId) tys)
> dataConstr cxL tc tvs (ConOpDecl _ _ cxR ty1 op ty2) =
>   con cxL tc tvs cxR op [(anonId,ty1),(anonId,ty2)]
> dataConstr cxL tc tvs (RecordDecl _ _ cxR c fs) =
>   con cxL tc tvs cxR c [(l,ty) | FieldDecl _ ls ty <- fs, l <- ls]

> newConstr :: [ClassAssert] -> QualIdent -> [Ident] -> NewConstrDecl
>           -> I ValueInfo
> newConstr cx tc tvs (NewConstrDecl _ c ty) = ncon cx tc tvs c anonId ty
> newConstr cx tc tvs (NewRecordDecl _ c l ty) = ncon cx tc tvs c l ty

> fieldLabel :: [ClassAssert] -> QualIdent -> [Ident] -> Ident -> TypeExpr
>            -> I ValueInfo
> fieldLabel cx tc tvs l ty =
>   (l,Value (qualifyLike tc l) 1 (typeScheme (toQualType ty')))
>   where ty' = QualTypeExpr cx (ArrowType (constrType tc tvs) ty)

> classMethod :: QualIdent -> Ident -> IMethodDecl -> I ValueInfo
> classMethod cls tv (IMethodDecl _ f ty) =
>   (f,Value (qualifyLike cls f) 0 (typeScheme (toMethodType cls tv ty)))

> qual :: QualIdent -> a -> [I a] -> [I a]
> qual x y = ((unqualify x,y) :)

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

> cidents :: QualIdent -> [Ident] -> [Ident] -> [I ValueKind] -> [I ValueKind]
> cidents tc xs cs = (map (cident tc) (filter (`notElem` xs) cs) ++)

> cident :: QualIdent -> Ident -> I ValueKind
> cident tc c = (c,Constr (qualifyLike tc c))

> lidents :: QualIdent -> [Ident] -> [(Ident,[Ident])] -> [I ValueKind]
>         -> [I ValueKind]
> lidents tc xs ls = (map (uncurry (lident tc)) ls' ++)
>   where ls' = filter ((`notElem` xs) . fst) ls

> lident :: QualIdent -> Ident -> [Ident] -> I ValueKind
> lident tc l cs = (l,Var (qualifyLike tc l) (map (qualifyLike tc) cs))

> midents :: QualIdent -> [Ident] -> [Ident] -> [I ValueKind] -> [I ValueKind]
> midents cls fs' fs = (map (mident cls) (filter (`notElem` fs') fs) ++)

> mident :: QualIdent -> Ident -> I ValueKind
> mident cls f = (f,Var (qualifyLike cls f) [])

> typeCon :: (QualIdent -> Kind -> a) -> QualIdent -> Maybe KindExpr -> [Ident]
>         -> a
> typeCon f tc k tvs = f tc (maybe (simpleKind (length tvs)) toKind k)

> typeCls :: [ClassAssert] -> QualIdent -> Maybe KindExpr -> Ident -> [Ident]
>         -> TypeInfo
> typeCls cx cls k tv =
>   TypeClass cls (maybe KindStar toKind k) [cls | TypePred cls _ <- cx']
>   where QualType cx' _ = toQualType (QualTypeExpr cx (VariableType tv))

> con :: [ClassAssert] -> QualIdent -> [Ident] -> [ClassAssert] -> Ident
>     -> [(Ident,TypeExpr)] -> I ValueInfo
> con cxL tc tvs cxR c tys =
>   (c,DataConstructor (qualifyLike tc c) ls ci (typeScheme ty))
>   where (ci,ty) = toConstrType cxL tc tvs cxR tys'
>         (ls,tys') = unzip tys

> ncon :: [ClassAssert] -> QualIdent -> [Ident] -> Ident -> Ident -> TypeExpr
>      -> I ValueInfo
> ncon cx tc tvs c l ty =
>   (c,NewtypeConstructor (qualifyLike tc c) l (typeScheme ty'))
>   where ty' = snd (toConstrType cx tc tvs [] [ty])

> constrType :: QualIdent -> [Ident] -> TypeExpr
> constrType tc tvs =
>   foldl ApplyType (ConstructorType tc) (map VariableType tvs)

\end{verbatim}
