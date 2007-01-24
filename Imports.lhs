% -*- LaTeX -*-
% $Id: Imports.lhs 2082 2007-01-24 20:11:46Z wlux $
%
% Copyright (c) 2000-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Imports.lhs}
\section{Importing Interfaces}
This module provides a few functions which can be used to import
interfaces into the current module.
\begin{verbatim}

> module Imports(importInterface,importInterfaceIntf,importUnifyData) where
> import Base
> import Env
> import Maybe
> import Map
> import Set
> import TopEnv
> import TypeTrans

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

> importInterface :: ModuleIdent -> Bool -> Maybe ImportSpec
>                 -> (PEnv,TCEnv,InstEnv,ValueEnv) -> Interface
>                 -> (PEnv,TCEnv,InstEnv,ValueEnv)
> importInterface m q is (pEnv,tcEnv,iEnv,tyEnv) (Interface m' _ ds) =
>   (importEntities precs m q vs id m' ds' pEnv,
>    importEntities types m q ts (importMembers vs) m' ds' tcEnv,
>    importInstances m' ds' iEnv,
>    importEntities values m q vs id m' ds' tyEnv)
>   where ds' = filter (not . isHiddenDecl) ds
>         ts = isVisible addType is
>         vs = isVisible addValue is

> isHiddenDecl :: IDecl -> Bool
> isHiddenDecl (IInfixDecl _ _ _ _) = False
> isHiddenDecl (HidingDataDecl _ _ _) = True 
> isHiddenDecl (IDataDecl _ _ _ _ _) = False
> isHiddenDecl (INewtypeDecl _ _ _ _ _) = False
> isHiddenDecl (ITypeDecl _ _ _ _) = False
> isHiddenDecl (HidingClassDecl _ _ _ _) = True
> isHiddenDecl (IClassDecl _ _ _ _ _) = False
> isHiddenDecl (IInstanceDecl _ _ _ _) = False
> isHiddenDecl (IFunctionDecl _ _ _) = False

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

> importMembers :: (Ident -> Bool) -> TypeInfo -> TypeInfo
> importMembers isVisible (DataType tc n cs) =
>   DataType tc n (map (>>= importMember isVisible) cs)
> importMembers isVisible (RenamingType tc n nc) =
>   maybe (DataType tc n []) (RenamingType tc n) (importMember isVisible nc)
> importMembers isVisible (AliasType tc n ty) = AliasType tc n ty
> importMembers isVisible (TypeClass cls clss fs) =
>   TypeClass cls clss (map (>>= importMember isVisible) fs)

> importMember :: (Ident -> Bool) -> Ident -> Maybe Ident
> importMember isVisible c
>   | isVisible c = Just c
>   | otherwise = Nothing

> importInstances :: ModuleIdent -> [IDecl] -> InstEnv -> InstEnv
> importInstances m ds iEnv = foldr (bindInstance m) iEnv ds

> bindInstance :: ModuleIdent -> IDecl -> InstEnv -> InstEnv
> bindInstance m (IInstanceDecl _ cx cls ty) =
>   bindEnv (CT (qualQualify m cls) (rootOfType ty')) cx'
>   where QualType cx' ty' = toQualType m (QualTypeExpr cx ty)
> bindInstance _ _ = id

\end{verbatim}
Importing an interface into another interface is somewhat simpler
because all entities are imported into the environments. In addition,
only a qualified import is necessary. Only those entities that are
actually defined in the module are imported. Since the compiler
imports all used interfaces into other interfaces, entities defined in
one module and re-exported by another module are made available by
their defining modules. Furthermore, ignoring re-exported entities
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
>   where ds' = filter (isJust . localIdent m . entity) ds

> entity :: IDecl -> QualIdent
> entity (IInfixDecl _ _ _ op) = op
> entity (HidingDataDecl _ tc _) = tc
> entity (IDataDecl _ _ tc _ _) = tc
> entity (INewtypeDecl _ _ tc _ _) = tc
> entity (ITypeDecl _ tc _ _) = tc
> entity (HidingClassDecl _ _ cls _) = cls
> entity (IClassDecl _ _ cls _ _) = cls
> entity (IInstanceDecl _ _ _ _) = qualify anonId
> entity (IFunctionDecl _ f _) = f

> importEntitiesIntf :: Entity a
>                    => (ModuleIdent -> IDecl -> [I a] -> [I a])
>                    -> ModuleIdent -> [IDecl] -> TopEnv a -> TopEnv a
> importEntitiesIntf bind m ds env =
>   foldr (uncurry (qualImportTopEnv m)) env (foldr (bind m) [] ds)

\end{verbatim}
The list of entities exported from a module is computed with the
following functions.
\begin{verbatim}

> precs :: ModuleIdent -> IDecl -> [I PrecInfo] -> [I PrecInfo]
> precs m (IInfixDecl _ fix p op) =
>   qual op (PrecInfo (qualQualify m op) (OpPrec fix p))
> precs _ _ = id

> types :: ModuleIdent -> IDecl -> [I TypeInfo] -> [I TypeInfo]
> types m (HidingDataDecl _ tc tvs) = qual tc (typeCon DataType m tc tvs [])
> types m (IDataDecl _ _ tc tvs cs) =
>   qual tc (typeCon DataType m tc tvs (map (fmap constr) cs))
> types m (INewtypeDecl _ _ tc tvs nc) =
>   qual tc (typeCon RenamingType m tc tvs (nconstr nc))
> types m (ITypeDecl _ tc tvs ty) =
>   qual tc (typeCon AliasType m tc tvs (toType m tvs ty))
> types m (HidingClassDecl _ cx cls tv) = qual cls (typeCls m cx cls tv [])
> types m (IClassDecl _ cx cls tv fs) =
>   qual cls (typeCls m cx cls tv (map (fmap imethod) fs))
> types _ _ = id

> values :: ModuleIdent -> IDecl -> [I ValueInfo] -> [I ValueInfo]
> values m (IDataDecl _ cx tc tvs cs) =
>   (map (dataConstr m cx (qualQualify m tc) tvs) (catMaybes cs) ++)
> values m (INewtypeDecl _ cx tc tvs nc) =
>   (newConstr m cx (qualQualify m tc) tvs nc :)
> values m (IFunctionDecl _ f ty) =
>   qual f (Value (qualQualify m f) (typeScheme (toQualType m ty)))
> values m (IClassDecl _ _ cls tv ds) =
>   (map (classMethod m (qualQualify m cls) tv) (catMaybes ds) ++)
> values _ _ = id

> dataConstr :: ModuleIdent -> [ClassAssert] -> QualIdent -> [Ident]
>            -> ConstrDecl -> I ValueInfo
> dataConstr m cx tc tvs (ConstrDecl _ _ c tys) =
>   (c,con DataConstructor m cx tc tvs c tys)
> dataConstr m cx tc tvs (ConOpDecl _ _ ty1 op ty2) =
>   (op,con DataConstructor m cx tc tvs op [ty1,ty2])

> newConstr :: ModuleIdent -> [ClassAssert] -> QualIdent -> [Ident]
>           -> NewConstrDecl -> I ValueInfo
> newConstr m cx tc tvs (NewConstrDecl _ c ty) =
>   (c,con NewtypeConstructor m cx tc tvs c [ty])

> classMethod :: ModuleIdent -> QualIdent -> Ident -> IMethodDecl -> I ValueInfo
> classMethod m cls tv (IMethodDecl _ f ty) =
>   (f,Value (qualifyLike cls f) (typeScheme (toMethodType m cls tv ty)))

> qual :: QualIdent -> a -> [I a] -> [I a]
> qual x y = ((unqualify x,y) :)

\end{verbatim}
After all modules have been imported, the compiler has to ensure that
all references to a data type use the same list of constructors.
\begin{verbatim}

> importUnifyData :: TCEnv -> TCEnv
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

> typeCon :: (QualIdent -> Int -> a) -> ModuleIdent -> QualIdent -> [Ident] -> a
> typeCon f m tc tvs = f (qualQualify m tc) (length tvs)

> typeCls :: ModuleIdent -> [ClassAssert] -> QualIdent -> Ident -> [Maybe Ident]
>         -> TypeInfo
> typeCls m cx cls tv =
>   TypeClass (qualQualify m cls) [cls | TypePred cls _ <- cx']
>   where QualType cx' _ = toQualType m (QualTypeExpr cx (VariableType tv))

> con :: (QualIdent -> TypeScheme -> a) -> ModuleIdent -> [ClassAssert]
>     -> QualIdent -> [Ident] -> Ident -> [TypeExpr] -> a
> con f m cx tc tvs c tys =
>   f (qualifyLike tc c) (typeScheme (toConstrType m cx tc tvs tys))

\end{verbatim}
