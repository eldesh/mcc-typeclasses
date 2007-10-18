% -*- LaTeX -*-
% $Id: Imports.lhs 2517 2007-10-18 14:23:42Z wlux $
%
% Copyright (c) 2000-2007, Wolfgang Lux
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
> import Maybe
> import Map
> import PrecInfo
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
> importIdents m q is (tEnv,iSet,vEnv) (Interface m' _ ds) =
>   (importEntities tidents m q ts (importMembers vs) m' ds tEnv,
>    importCTs m' ds iSet,
>    importEntities vidents m q vs id m' ds vEnv)
>   where ts = isVisible addType is
>         vs = isVisible addValue is

> importInterface :: ModuleIdent -> Bool -> Maybe ImportSpec
>                 -> (PEnv,TCEnv,InstEnv,ValueEnv) -> Interface
>                 -> (PEnv,TCEnv,InstEnv,ValueEnv)
> importInterface m q is (pEnv,tcEnv,iEnv,tyEnv) (Interface m' _ ds) =
>   (importEntities precs m q vs id m' ds pEnv,
>    importEntities types m q ts id m' ds tcEnv,
>    importInstances m' ds iEnv,
>    importEntities values m q vs id m' ds tyEnv)
>   where ts = isVisible addType is
>         vs = isVisible addValue is

> isVisible :: (Import -> Set Ident -> Set Ident) -> Maybe ImportSpec
>           -> Ident -> Bool
> isVisible add (Just (Importing _ xs)) = (`elemSet` foldr add zeroSet xs)
> isVisible add (Just (Hiding _ xs)) = (`notElemSet` foldr add zeroSet xs)
> isVisible _ Nothing = const True

> importEntities :: Entity a
>                => (ModuleIdent -> IDecl -> [I a] -> [I a])
>                -> ModuleIdent -> Bool -> (Ident -> Bool) -> (a -> a)
>                -> ModuleIdent -> [IDecl] -> TopEnv a -> TopEnv a
> importEntities bind m q isVisible f m' ds env =
>   foldr (uncurry (importTopEnv q m)) env
>         [(x,f y) | (x,y) <- foldr (bind m') [] ds, isVisible x]

> importMembers :: (Ident -> Bool) -> TypeKind -> TypeKind
> importMembers isVisible (Data tc cs) = Data tc (filter isVisible cs)
> importMembers _ (Alias tc) = Alias tc
> importMembers isVisible (Class cls fs) = Class cls (filter isVisible fs)

> importMember :: (Ident -> Bool) -> Ident -> Maybe Ident
> importMember isVisible c
>   | isVisible c = Just c
>   | otherwise = Nothing

> importCTs :: ModuleIdent -> [IDecl] -> InstSet -> InstSet
> importCTs m ds iEnv = foldr (addCT m) iEnv ds

> addCT :: ModuleIdent -> IDecl -> InstSet -> InstSet
> addCT m (IInstanceDecl _ _ cls ty _) =
>   addToSet (CT (qualQualify m cls) (qualQualify m (typeConstr ty)))
> addCT _ _ = id

> importInstances :: ModuleIdent -> [IDecl] -> InstEnv -> InstEnv
> importInstances m ds iEnv = foldr (bindInstance m) iEnv ds

> bindInstance :: ModuleIdent -> IDecl -> InstEnv -> InstEnv
> bindInstance m (IInstanceDecl _ cx cls ty m') =
>   bindEnv (CT (qualQualify m cls) (rootOfType ty')) (fromMaybe m m',cx')
>   where QualType cx' ty' = toQualType m (QualTypeExpr cx ty)
> bindInstance _ _ = id

\end{verbatim}
Importing an interface into another interface is somewhat simpler
because all entities are imported into the environments. In addition,
only a qualified import is necessary. Only those entities that are
actually defined in the module are imported. Since the compiler
imports all used interfaces into other interfaces, entities defined in
one module and reexported by another module are made available by
their defining modules. Furthermore, ignoring reexported entities
avoids a problem with the fact that the unqualified names of entities
defined in an interface may be ambiguous if hidden data type and class
declarations are taken into account. For instance, in the interface
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
>    importInstances m ds' iEnv,
>    importEntitiesIntf values m ds' tyEnv)
>   where ds' = map unhide (filter (isJust . localIdent m . entity) ds)

> entity :: IDecl -> QualIdent
> entity (IInfixDecl _ _ _ op) = op
> entity (HidingDataDecl _ tc _ _) = tc
> entity (IDataDecl _ _ tc _ _ _ _) = tc
> entity (INewtypeDecl _ _ tc _ _ _) = tc
> entity (ITypeDecl _ tc _ _ _) = tc
> entity (HidingClassDecl _ _ cls _ _) = cls
> entity (IClassDecl _ _ cls _ _ _) = cls
> entity (IInstanceDecl _ _ _ _ _) = qualify anonId
> entity (IFunctionDecl _ f _ _) = f

> unhide :: IDecl -> IDecl
> unhide (IInfixDecl p fix pr op) = IInfixDecl p fix pr op
> unhide (HidingDataDecl p tc k tvs) = IDataDecl p [] tc k tvs [] []
> unhide (IDataDecl p cx tc k tvs cs _) = IDataDecl p cx tc k tvs cs []
> unhide (INewtypeDecl p cx tc k tvs nc) = INewtypeDecl p cx tc k tvs nc
> unhide (ITypeDecl p tc k tvs ty) = ITypeDecl p tc k tvs ty
> unhide (HidingClassDecl p cx cls k tv) = IClassDecl p cx cls k tv []
> unhide (IClassDecl p cx cls k tv ds) = IClassDecl p cx cls k tv ds
> unhide (IInstanceDecl p cx cls ty m) = IInstanceDecl p cx cls ty m
> unhide (IFunctionDecl p f n ty) = IFunctionDecl p f n ty

> importEntitiesIntf :: Entity a
>                    => (ModuleIdent -> IDecl -> [I a] -> [I a])
>                    -> ModuleIdent -> [IDecl] -> TopEnv a -> TopEnv a
> importEntitiesIntf bind m ds env =
>   foldr (uncurry (qualImportTopEnv m)) env (foldr (bind m) [] ds)

\end{verbatim}
The list of entities exported from a module is computed with the
following functions.
\begin{verbatim}

> tidents :: ModuleIdent -> IDecl -> [I TypeKind] -> [I TypeKind]
> tidents m (IDataDecl _ _ tc _ _ cs cs') =
>   qual tc (tident Data m tc (filter (`notElem` cs') (map constr cs)))
> tidents m (INewtypeDecl _ _ tc _ _ nc) =
>   qual tc (tident Data m tc [nconstr nc])
> tidents m (ITypeDecl _ tc _ _ _) = qual tc (tident Alias m tc)
> tidents m (IClassDecl _ _ cls _ _ ds) =
>   qual cls (tident Class m cls (map imethod (catMaybes ds)))
> tidents _ _ = id

> vidents :: ModuleIdent -> IDecl -> [I ValueKind] -> [I ValueKind]
> vidents m (IDataDecl _ _ tc _ _ cs cs') =
>   (map (cident (qualQualify m tc)) cs'' ++)
>   where cs'' = filter (`notElem` cs') (map constr cs)
> vidents m (INewtypeDecl _ _ tc _ _ nc) =
>   (cident (qualQualify m tc) (nconstr nc) :)
> vidents m (IClassDecl _ _ cls _ _ ds) =
>   (map (mident (qualQualify m cls) . imethod) (catMaybes ds) ++)
> vidents m (IFunctionDecl _ f _ _) = qual f (Var (qualQualify m f))
> vidents _ _ = id

> precs :: ModuleIdent -> IDecl -> [I PrecInfo] -> [I PrecInfo]
> precs m (IInfixDecl _ fix p op) =
>   qual op (PrecInfo (qualQualify m op) (OpPrec fix p))
> precs _ _ = id

> types :: ModuleIdent -> IDecl -> [I TypeInfo] -> [I TypeInfo]
> types m (IDataDecl _ _ tc k tvs cs _) =
>   qual tc (typeCon DataType m tc k tvs (map constr cs))
> types m (INewtypeDecl _ _ tc k tvs nc) =
>   qual tc (typeCon RenamingType m tc k tvs (nconstr nc))
> types m (ITypeDecl _ tc k tvs ty) =
>   qual tc (typeCon (flip AliasType (length tvs)) m tc k tvs (toType m tvs ty))
> types m (IClassDecl _ cx cls k tv ds) =
>   qual cls (typeCls m cx cls k tv (map (fmap imethod) ds))
> types _ _ = id

> values :: ModuleIdent -> IDecl -> [I ValueInfo] -> [I ValueInfo]
> values m (IDataDecl _ cx tc _ tvs cs cs') =
>   (map (dataConstr m cx (qualQualify m tc) tvs) cs'' ++)
>   where cs'' = filter ((`notElem` cs') . constr) cs
> values m (INewtypeDecl _ cx tc _ tvs nc) =
>   (newConstr m cx (qualQualify m tc) tvs nc :)
> values m (IClassDecl _ _ cls _ tv ds) =
>   (map (classMethod m (qualQualify m cls) tv) (catMaybes ds) ++)
> values m (IFunctionDecl _ f n ty) =
>   qual f (Value (qualQualify m f) n' (typeScheme ty'))
>   where n' = maybe (arrowArity (unqualType ty')) fromInteger n
>         ty' = toQualType m ty
> values _ _ = id

> dataConstr :: ModuleIdent -> [ClassAssert] -> QualIdent -> [Ident]
>            -> ConstrDecl -> I ValueInfo
> dataConstr m cxL tc tvs (ConstrDecl _ _ cxR c tys) =
>   (c,con DataConstructor m cxL tc tvs cxR c tys)
> dataConstr m cxL tc tvs (ConOpDecl _ _ cxR ty1 op ty2) =
>   (op,con DataConstructor m cxL tc tvs cxR op [ty1,ty2])

> newConstr :: ModuleIdent -> [ClassAssert] -> QualIdent -> [Ident]
>           -> NewConstrDecl -> I ValueInfo
> newConstr m cx tc tvs (NewConstrDecl _ c ty) =
>   (c,con (const . const . NewtypeConstructor) m cx tc tvs [] c [ty])

> classMethod :: ModuleIdent -> QualIdent -> Ident -> IMethodDecl -> I ValueInfo
> classMethod m cls tv (IMethodDecl _ f ty) =
>   (f,Value (qualifyLike cls f) 0 (typeScheme (toMethodType m cls tv ty)))

> qual :: QualIdent -> a -> [I a] -> [I a]
> qual x y = ((unqualify x,y) :)

\end{verbatim}
After all modules have been imported, the compiler has to ensure that
all references to a data type use the same list of constructors.
\begin{verbatim}

> importUnifyData :: TypeEnv -> TypeEnv
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

> tident :: (QualIdent -> a) -> ModuleIdent -> QualIdent -> a
> tident f m tc = f (qualQualify m tc)

> cident :: QualIdent -> Ident -> I ValueKind
> cident tc c = (c,Constr (qualifyLike tc c))

> mident :: QualIdent -> Ident -> I ValueKind
> mident cls f = (f,Var (qualifyLike cls f))

> typeCon :: (QualIdent -> Kind -> a) -> ModuleIdent -> QualIdent
>         -> Maybe KindExpr -> [Ident] -> a
> typeCon f m tc k tvs =
>   f (qualQualify m tc) (maybe (simpleKind (length tvs)) toKind k)

> typeCls :: ModuleIdent -> [ClassAssert] -> QualIdent -> Maybe KindExpr
>         -> Ident -> [Maybe Ident] -> TypeInfo
> typeCls m cx cls k tv =
>   TypeClass (qualQualify m cls) (maybe KindStar toKind k)
>             [cls | TypePred cls _ <- cx']
>   where QualType cx' _ = toQualType m (QualTypeExpr cx (VariableType tv))

> con :: (QualIdent -> Int -> ConstrInfo -> TypeScheme -> a) -> ModuleIdent
>     -> [ClassAssert] -> QualIdent -> [Ident] -> [ClassAssert] -> Ident
>     -> [TypeExpr] -> a
> con f m cxL tc tvs cxR c tys =
>   f (qualifyLike tc c) (length tys) ci (typeScheme ty)
>   where (ci,ty) = toConstrType m cxL tc tvs cxR tys

\end{verbatim}
