% -*- LaTeX -*-
% $Id: Exports.lhs 1974 2006-09-21 09:25:16Z wlux $
%
% Copyright (c) 2000-2006, Wolfgang Lux
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
> import Maybe
> import Set
> import TopEnv
> import TypeTrans

> exportInterface :: ModuleIdent -> ExportSpec
>                 -> PEnv -> TCEnv -> InstEnv -> ValueEnv -> Interface
> exportInterface m (Exporting _ es) pEnv tcEnv iEnv tyEnv =
>   Interface m imports (precs ++ hidden ++ ds)
>   where imports = map (IImportDecl noPos) (usedModules ds)
>         precs = foldr (infixDecl m pEnv) [] es
>         hidden = map (hiddenTypeDecl m tcEnv) (hiddenTypes ds)
>         ds = types ++ values ++ insts
>         types = foldr (typeDecl m tcEnv tyEnv) [] es
>         values = foldr (funDecl m tyEnv) [] es
>         insts = foldr (instDecl m tcEnv ts) [] (toListSet iEnv)
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
> typeDecl m tcEnv tyEnv (ExportTypeWith tc cs) ds =
>   case qualLookupTopEnv tc tcEnv of
>     [DataType _ n cs'] -> iTypeDecl IDataDecl m tc n constrs : ds
>       where constrs evs
>               | null cs = []
>               | otherwise =
>                   map (>>= fmap (constrDecl m tyEnv tc n evs) . hide cs) cs'
>             hide cs c
>               | c `elem` cs = Just c
>               | otherwise = Nothing
>     [RenamingType _ n c]
>       | null cs -> iTypeDecl IDataDecl m tc n (const []) : ds
>       | otherwise -> iTypeDecl INewtypeDecl m tc n newConstr : ds
>       where newConstr _ = newConstrDecl m tyEnv tc c
>     [AliasType _ n ty] ->
>       iTypeDecl ITypeDecl m tc n (const (fromType m ty)) : ds
>     [TypeClass _] ->
>       IClassDecl noPos (qualUnqualify m tc) (head nameSupply) : ds
>     _ -> internalError "typeDecl"

> iTypeDecl :: (Position -> QualIdent -> [Ident] -> a -> IDecl)
>           -> ModuleIdent -> QualIdent -> Int -> ([Ident] -> a) -> IDecl
> iTypeDecl f m tc n g = f noPos (qualUnqualify m tc) tvs (g tvs')
>   where (tvs,tvs') = splitAt n nameSupply

> constrDecl :: ModuleIdent -> ValueEnv -> QualIdent -> Int -> [Ident]
>            -> Ident -> ConstrDecl
> constrDecl m tyEnv tc n evs c =
>   ConstrDecl noPos (take (n' - n) evs) c (map (fromType m) (arrowArgs ty))
>   where ForAll n' ty = conType (qualifyLike tc c) tyEnv

> newConstrDecl :: ModuleIdent -> ValueEnv -> QualIdent -> Ident
>               -> NewConstrDecl
> newConstrDecl m tyEnv tc c =
>   NewConstrDecl noPos c (fromType m (head (arrowArgs ty)))
>   where ForAll _ ty = conType (qualifyLike tc c) tyEnv

> funDecl :: ModuleIdent -> ValueEnv -> Export -> [IDecl] -> [IDecl]
> funDecl m tyEnv (Export f) ds =
>   IFunctionDecl noPos (qualUnqualify m f) (fromType m ty) : ds
>   where ty = rawType (funType f tyEnv)
> funDecl _ _ (ExportTypeWith _ _) ds = ds

> instDecl :: ModuleIdent -> TCEnv -> [QualIdent] -> CT -> [IDecl] -> [IDecl]
> instDecl m tcEnv ts (CT cls tc) ds
>   | isJust (localIdent m cls) && cls `notElem` ts = ds
>   | isJust (localIdent m tc) && not (isPrimTypeId tc) && tc `notElem` ts = ds
>   | otherwise = IInstanceDecl noPos (qualUnqualify m cls) (fromType m ty) : ds
>   where ty
>           | tc == qArrowId = TypeArrow (tvs !! 0) (tvs !! 1)
>           | otherwise = TypeConstructor tc (take (constrKind tc tcEnv) tvs)
>         tvs = map TypeVariable [0..]

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
>   modules (IDataDecl _ tc _ cs) = modules tc . modules cs
>   modules (INewtypeDecl _ tc _ nc) = modules tc . modules nc
>   modules (ITypeDecl _ tc _ ty) = modules tc . modules ty
>   modules (IClassDecl _ cls _) = modules cls
>   modules (IInstanceDecl _ cls ty) = modules cls . modules ty
>   modules (IFunctionDecl _ f ty) = modules f . modules ty

> instance HasModule ConstrDecl where
>   modules (ConstrDecl _ _ _ tys) = modules tys
>   modules (ConOpDecl _ _ ty1 _ ty2) = modules ty1 . modules ty2

> instance HasModule NewConstrDecl where
>   modules (NewConstrDecl _ _ ty) = modules ty

> instance HasModule TypeExpr where
>   modules (ConstructorType tc tys) = modules tc . modules tys
>   modules (VariableType _) = id
>   modules (TupleType tys) = modules tys
>   modules (ListType ty) = modules ty
>   modules (ArrowType ty1 ty2) = modules ty1 . modules ty2

> instance HasModule QualIdent where
>   modules = maybe id (:) . fst . splitQualIdent

\end{verbatim}
After the interface declarations have been computed, the compiler adds
hidden (data) type declarations to the interface for all types which
were used in the interface but are not exported from it. This is
necessary in order to distinguish type constructors and type
variables. Furthermore, by including hidden types in interfaces the
compiler can check them without loading the imported modules.
\begin{verbatim}

> hiddenTypeDecl :: ModuleIdent -> TCEnv -> QualIdent -> IDecl
> hiddenTypeDecl m tcEnv tc = HidingDataDecl noPos tc (take n nameSupply)
>   where n = constrKind (qualQualify m tc) tcEnv

> hiddenTypes :: [IDecl] -> [QualIdent]
> hiddenTypes ds =
>   filter (not . isPrimTypeId) (toListSet (foldr deleteFromSet used defd))
>   where used = fromListSet (usedTypes ds [])
>         defd = foldr definedType [] ds

> definedType :: IDecl -> [QualIdent] -> [QualIdent]
> definedType (IDataDecl _ tc _ _) tcs = tc : tcs
> definedType (INewtypeDecl _ tc _ _) tcs = tc : tcs
> definedType (ITypeDecl _ tc _ _) tcs = tc : tcs
> definedType (IClassDecl _ _ _) tcs = tcs
> definedType (IInstanceDecl _ _ _) tcs = tcs
> definedType (IFunctionDecl _ _ _)  tcs = tcs

> class HasType a where
>   usedTypes :: a -> [QualIdent] -> [QualIdent]

> instance HasType a => HasType (Maybe a) where
>   usedTypes = maybe id usedTypes

> instance HasType a => HasType [a] where
>   usedTypes xs tcs = foldr usedTypes tcs xs

> instance HasType IDecl where
>   usedTypes (IDataDecl _ _ _ cs) = usedTypes cs
>   usedTypes (INewtypeDecl _ _ _ nc) = usedTypes nc
>   usedTypes (ITypeDecl _ _ _ ty) = usedTypes ty
>   usedTypes (IClassDecl _ _ _) = id
>   usedTypes (IInstanceDecl _ _ ty) = usedTypes ty
>   usedTypes (IFunctionDecl _ _ ty) = usedTypes ty

> instance HasType ConstrDecl where
>   usedTypes (ConstrDecl _ _ _ tys) = usedTypes tys
>   usedTypes (ConOpDecl _ _ ty1 _ ty2) = usedTypes ty1 . usedTypes ty2

> instance HasType NewConstrDecl where
>   usedTypes (NewConstrDecl _ _ ty) = usedTypes ty

> instance HasType TypeExpr where
>   usedTypes (ConstructorType tc tys) = (tc :) . usedTypes tys
>   usedTypes (VariableType _) = id
>   usedTypes (TupleType tys) = usedTypes tys
>   usedTypes (ListType ty) = usedTypes ty
>   usedTypes (ArrowType ty1 ty2) = usedTypes ty1 . usedTypes ty2

\end{verbatim}
Auxiliary definitions.
\begin{verbatim}

> noPos :: Position
> noPos = undefined

\end{verbatim}
