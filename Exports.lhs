% -*- LaTeX -*-
% $Id: Exports.lhs 2171 2007-04-24 21:53:08Z wlux $
%
% Copyright (c) 2000-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Exports.lhs}
\section{Creating Interfaces}
After checking a module, the compiler generates the interface's
declarations from the list of exported types and values. If an entity
is imported from another module, its name is qualified with the name
of the module containing its definition. Furthermore, newtypes whose
constructor is not exported are transformed into (abstract) data
types. In principle, all instance declarations visible in the current
module (whether defined locally or imported from another module) must
be exported. However, there is no point in exporting local instance
declarations which cannot be used in another module because
\begin{enumerate}
\item the instance is defined for a private class of the current
  module, or
\item the instance is defined for a private type of the current
  module that furthermore does not occur in any of the interface's
  type signatures.
\end{enumerate}
\begin{verbatim}

> module Exports(exportInterface) where
> import Base
> import Env
> import KindTrans
> import List
> import Maybe
> import Set
> import TopEnv
> import TypeTrans

> exportInterface :: Module a -> PEnv -> TCEnv -> InstEnv -> ValueEnv
>                 -> Interface
> exportInterface (Module m (Just (Exporting _ es)) _ _) pEnv tcEnv iEnv tyEnv =
>   Interface m imports (precs ++ hidden ++ ds)
>   where imports = map (IImportDecl noPos) (usedModules ds)
>         precs = foldr (infixDecl m pEnv) [] es
>         hidden = map (hiddenTypeDecl m tcEnv) (hiddenTypes ds)
>         ds = types ++ values ++ insts
>         types = foldr (typeDecl m tcEnv tyEnv) [] es
>         values = foldr (funDecl m tcEnv tyEnv) [] es
>         insts = foldr (uncurry (instDecl m tcEnv ts)) [] (envToList iEnv)
>         ts = [tc | ExportTypeWith tc _ <- es] ++
>              map (qualQualify m) (hiddenTypes values)

> infixDecl :: ModuleIdent -> PEnv -> Export -> [IDecl] -> [IDecl]
> infixDecl m pEnv (Export f) ds = iInfixDecl m pEnv f ds
> infixDecl m pEnv (ExportTypeWith tc cs) ds =
>   foldr (iInfixDecl m pEnv . qualifyLike tc) ds cs

> iInfixDecl :: ModuleIdent -> PEnv -> QualIdent -> [IDecl] -> [IDecl]
> iInfixDecl m pEnv op ds =
>   case qualLookupTopEnv op pEnv of
>     [] -> ds
>     [PrecInfo _ (OpPrec fix pr)] ->
>       IInfixDecl noPos fix pr (qualUnqualify m op) : ds
>     _ -> internalError "infixDecl"

> typeDecl :: ModuleIdent -> TCEnv -> ValueEnv -> Export -> [IDecl] -> [IDecl]
> typeDecl _ _ _ (Export _) ds = ds
> typeDecl m tcEnv tyEnv (ExportTypeWith tc xs) ds =
>   case qualLookupTopEnv tc tcEnv of
>     [DataType _ k cs] -> iTypeDecl IDataDecl m tcEnv tc n k constrs : ds
>       where n = kindArity k
>             constrs tvs
>               | null xs = ([],[])
>               | otherwise = (orderContext tvs (nub cx'),cs')
>               where (cx',cs') =
>                       mapAccumR mergeContext [] $
>                       map (hideDecl (constrDecl tcEnv tyEnv tc tvs) xs) cs
>             mergeContext cx c = (maybe [] fst c ++ cx,fmap snd c)
>     [RenamingType _ k c]
>       | null xs -> iTypeDecl IDataDecl m tcEnv tc n k (const ([],[])) : ds
>       | otherwise -> iTypeDecl INewtypeDecl m tcEnv tc n k newConstr : ds
>       where n = kindArity k
>             newConstr _ = newConstrDecl tcEnv tyEnv tc c
>     [AliasType _ n k ty] ->
>       iTypeDecl (const . ITypeDecl) m tcEnv tc n k (const ([],ty')) : ds
>       where ty' = fromType tcEnv ty
>     [TypeClass _ k clss fs] ->
>       iClassDecl IClassDecl m tcEnv tc k clss (methods fs) : ds
>       where methods fs = map (hideDecl (methodDecl tcEnv tyEnv tc) xs) fs
>     _ -> internalError "typeDecl"
>   where hideDecl f xs x = x >>= fmap f . hide xs
>         hide xs x
>           | x `elem` xs = Just x
>           | otherwise = Nothing

> iTypeDecl :: (Position -> [ClassAssert] -> QualIdent -> Maybe KindExpr
>               -> [Ident] -> a -> IDecl)
>           -> ModuleIdent -> TCEnv -> QualIdent -> Int -> Kind
>           -> ([Ident] -> ([ClassAssert],a)) -> IDecl
> iTypeDecl f m tcEnv tc n k g = f noPos cx (qualUnqualify m tc) k' tvs' x
>   where k' = if k == simpleKind n then Nothing else Just (fromKind k)
>         tvs = map TypeVariable (take n [0..])
>         tvs' = fv (fromType tcEnv (foldl TypeApply (TypeConstructor tc) tvs))
>         (cx,x) = g tvs'

> iClassDecl :: (Position -> [ClassAssert] -> QualIdent -> Maybe KindExpr
>                -> Ident -> a)
>            -> ModuleIdent -> TCEnv -> QualIdent -> Kind -> [QualIdent] -> a
> iClassDecl f m tcEnv cls k clss = f noPos cx (qualUnqualify m cls) k' tv
>   where k' = if k == KindStar then Nothing else Just (fromKind k)
>         ty = TypeVariable 0
>         QualTypeExpr cx (VariableType tv) =
>           fromQualType tcEnv (QualType (map (flip TypePred ty) clss) ty)

> constrDecl :: TCEnv -> ValueEnv -> QualIdent -> [Ident] -> Ident
>            -> ([ClassAssert],ConstrDecl)
> constrDecl tcEnv tyEnv tc tvs c = (cx',ConstrDecl noPos evs c (argTypes ty'))
>   where evs = filter (`notElem` tvs) (nub (fv ty'))
>         ForAll _ (QualType cx ty) = conType (qualifyLike tc c) tyEnv
>         QualTypeExpr cx' ty' = fromQualType tcEnv (QualType cx ty)

> newConstrDecl :: TCEnv -> ValueEnv -> QualIdent -> Ident
>               -> ([ClassAssert],NewConstrDecl)
> newConstrDecl tcEnv tyEnv tc c =
>   (cx',NewConstrDecl noPos c (head (argTypes ty')))
>   where ForAll _ (QualType cx ty) = conType (qualifyLike tc c) tyEnv
>         QualTypeExpr cx' ty' = fromQualType tcEnv (QualType cx ty)

> methodDecl :: TCEnv -> ValueEnv -> QualIdent -> Ident -> IMethodDecl
> methodDecl tcEnv tyEnv cls f =
>   IMethodDecl noPos f (fromQualType tcEnv (QualType (tail cx) ty))
>   where ForAll _ (QualType cx ty) = funType (qualifyLike cls f) tyEnv

> funDecl :: ModuleIdent -> TCEnv -> ValueEnv -> Export -> [IDecl] -> [IDecl]
> funDecl m tcEnv tyEnv (Export f) ds =
>   IFunctionDecl noPos (qualUnqualify m f) n' (fromQualType tcEnv ty) : ds
>   where n = arity f tyEnv
>         n' =
>           if arrowArity (rawType (ForAll u ty)) == n then Nothing else Just n
>         ForAll u ty = funType f tyEnv
> funDecl _ _ _ (ExportTypeWith _ _) ds = ds

> instDecl :: ModuleIdent -> TCEnv -> [QualIdent] -> CT -> Context -> [IDecl]
>          -> [IDecl]
> instDecl m tcEnv ts (CT cls tc) cx ds
>   | isJust (localIdent m cls) && cls `notElem` ts = ds
>   | isJust (localIdent m tc) && not (isPrimTypeId tc) && tc `notElem` ts = ds
>   | otherwise = IInstanceDecl noPos cx' (qualUnqualify m cls) ty' : ds
>   where n = kindArity (constrKind tc tcEnv) - kindArity (classKind cls tcEnv)
>         tvs = take n (map TypeVariable [0..])
>         QualTypeExpr cx' ty' = fromQualType tcEnv $
>           QualType cx (applyType (TypeConstructor tc) tvs)

\end{verbatim}
The compiler determines the list of imported modules from the set of
module qualifiers that are used in the interface. Careful readers
probably will have noticed that the functions above carefully strip
the module prefix from all entities that are defined in the current
module. Note that the list of modules returned from
\texttt{usedModules} is not necessarily a subset of the modules that
were imported into the current module. This will happen when an
imported module re-exports entities from another module. E.g., given
the three modules
\begin{verbatim}
module A where { data A = A; }
module B(A(..)) where { import A; }
module C where { import B; x = A; }
\end{verbatim}
the interface for module \texttt{C} will import module \texttt{A} but
not module \texttt{B}.
\begin{verbatim}

> usedModules :: [IDecl] -> [ModuleIdent]
> usedModules ds = nub (modules ds [])
>   where nub = toListSet . fromListSet

> class HasModule a where
>   modules :: a -> [ModuleIdent] -> [ModuleIdent]

> instance HasModule a => HasModule (Maybe a) where
>   modules = maybe id modules

> instance HasModule a => HasModule [a] where
>   modules xs ms = foldr modules ms xs

> instance HasModule IDecl where
>   modules (IDataDecl _ cx tc _ _ cs) = modules cx . modules tc . modules cs
>   modules (INewtypeDecl _ cx tc _ _ nc) = modules cx . modules tc . modules nc
>   modules (ITypeDecl _ tc _ _ ty) = modules tc . modules ty
>   modules (IClassDecl _ cx cls _ _ ds) = modules cx . modules cls . modules ds
>   modules (IInstanceDecl _ cx cls ty) = modules cx . modules cls . modules ty
>   modules (IFunctionDecl _ f _ ty) = modules f . modules ty

> instance HasModule ConstrDecl where
>   modules (ConstrDecl _ _ _ tys) = modules tys
>   modules (ConOpDecl _ _ ty1 _ ty2) = modules ty1 . modules ty2

> instance HasModule NewConstrDecl where
>   modules (NewConstrDecl _ _ ty) = modules ty

> instance HasModule IMethodDecl where
>   modules (IMethodDecl _ _ ty) = modules ty

> instance HasModule QualTypeExpr where
>   modules (QualTypeExpr cx ty) = modules cx . modules ty

> instance HasModule ClassAssert where
>   modules (ClassAssert cls _ tys) = modules cls . modules tys

> instance HasModule TypeExpr where
>   modules (ConstructorType tc) = modules tc
>   modules (VariableType _) = id
>   modules (TupleType tys) = modules tys
>   modules (ListType ty) = modules ty
>   modules (ArrowType ty1 ty2) = modules ty1 . modules ty2
>   modules (ApplyType ty1 ty2) = modules ty1 . modules ty2

> instance HasModule QualIdent where
>   modules = maybe id (:) . fst . splitQualIdent

\end{verbatim}
After the interface declarations have been computed, the compiler adds
hidden (data) type and class declarations to the interface for all
types and classes which were used in the interface but are not
exported from it. This is necessary in order to distinguish type
constructors and type variables. Furthermore, by including hidden
types and classes in interfaces the compiler can check them without
loading the imported modules.
\begin{verbatim}

> hiddenTypeDecl :: ModuleIdent -> TCEnv -> QualIdent -> IDecl
> hiddenTypeDecl m tcEnv tc =
>   case qualLookupTopEnv (qualQualify m tc) tcEnv of
>     [DataType _ k _] ->
>       iTypeDecl hidingDataDecl m tcEnv tc (kindArity k) k undefined
>     [RenamingType _ k _] ->
>       iTypeDecl hidingDataDecl m tcEnv tc (kindArity k) k undefined
>     [TypeClass _ k clss _] -> iClassDecl HidingClassDecl m tcEnv tc k clss
>     _ -> internalError "hiddenTypeDecl"
>   where hidingDataDecl p _ tc k tvs _ = HidingDataDecl p tc k tvs

> hiddenTypes :: [IDecl] -> [QualIdent]
> hiddenTypes ds =
>   filter (not . isPrimTypeId) (toListSet (foldr deleteFromSet used defd))
>   where used = fromListSet (usedTypes ds [])
>         defd = foldr definedType [] ds

> definedType :: IDecl -> [QualIdent] -> [QualIdent]
> definedType (IDataDecl _ _ tc _ _ _) tcs = tc : tcs
> definedType (INewtypeDecl _ _ tc _ _ _) tcs = tc : tcs
> definedType (ITypeDecl _ tc _ _ _) tcs = tc : tcs
> definedType (IClassDecl _ _ cls _ _ _) tcs = cls : tcs
> definedType (IInstanceDecl _ _ _ _) tcs = tcs
> definedType (IFunctionDecl _ _ _ _)  tcs = tcs

> class HasType a where
>   usedTypes :: a -> [QualIdent] -> [QualIdent]

> instance HasType a => HasType (Maybe a) where
>   usedTypes = maybe id usedTypes

> instance HasType a => HasType [a] where
>   usedTypes xs tcs = foldr usedTypes tcs xs

> instance HasType IDecl where
>   usedTypes (IDataDecl _ cx _ _ _ cs) = usedTypes cx . usedTypes cs
>   usedTypes (INewtypeDecl _ cx _ _ _ nc) = usedTypes cx . usedTypes nc
>   usedTypes (ITypeDecl _ _ _ _ ty) = usedTypes ty
>   usedTypes (IClassDecl _ cx _ _ _ ds) = usedTypes cx . usedTypes ds
>   usedTypes (IInstanceDecl _ cx cls ty) =
>     usedTypes cx . (cls :) . usedTypes ty
>   usedTypes (IFunctionDecl _ _ _ ty) = usedTypes ty

> instance HasType ConstrDecl where
>   usedTypes (ConstrDecl _ _ _ tys) = usedTypes tys
>   usedTypes (ConOpDecl _ _ ty1 _ ty2) = usedTypes ty1 . usedTypes ty2

> instance HasType NewConstrDecl where
>   usedTypes (NewConstrDecl _ _ ty) = usedTypes ty

> instance HasType IMethodDecl where
>   usedTypes (IMethodDecl _ _ ty) = usedTypes ty

> instance HasType QualTypeExpr where
>   usedTypes (QualTypeExpr cx ty) = usedTypes cx . usedTypes ty

> instance HasType ClassAssert where
>   usedTypes (ClassAssert cls _ tys) = (cls :) . usedTypes tys

> instance HasType TypeExpr where
>   usedTypes (ConstructorType tc) = (tc :)
>   usedTypes (VariableType _) = id
>   usedTypes (TupleType tys) = usedTypes tys
>   usedTypes (ListType ty) = usedTypes ty
>   usedTypes (ArrowType ty1 ty2) = usedTypes ty1 . usedTypes ty2
>   usedTypes (ApplyType ty1 ty2) = usedTypes ty1 . usedTypes ty2

\end{verbatim}
Auxiliary definitions.
\begin{verbatim}

> noPos :: Position
> noPos = undefined

> orderContext :: [Ident] -> [ClassAssert] -> [ClassAssert]
> orderContext [] _ = []
> orderContext (tv:tvs) cx = cx' ++ orderContext tvs cx''
>   where (cx',cx'') = partition (\(ClassAssert _ tv' _) -> tv == tv') cx

> argTypes :: TypeExpr -> [TypeExpr]
> argTypes (ArrowType ty1 ty2) = ty1 : argTypes ty2
> argTypes _ = []

\end{verbatim}
