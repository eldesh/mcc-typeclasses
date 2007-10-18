% -*- LaTeX -*-
% $Id: Exports.lhs 2518 2007-10-18 15:27:42Z wlux $
%
% Copyright (c) 2000-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Exports.lhs}
\section{Creating Interfaces}
After checking a module, the compiler generates the interface's
declarations from the list of exported types and values. If an entity
is imported from another module, its name is qualified with the name
of the module containing its definition. Newtypes whose constructor is
not exported are transformed into (abstract) data types. Instances are
exported together with their classes and types as explained below.
\begin{verbatim}

> module Exports(exportInterface) where
> import Base
> import Curry
> import CurryUtils
> import Env
> import InstInfo
> import Kinds
> import KindTrans
> import List
> import Maybe
> import Monad
> import PrecInfo
> import Set
> import TopEnv
> import Types
> import TypeInfo
> import TypeTrans
> import ValueInfo

> exportInterface :: Module a -> PEnv -> TCEnv -> InstEnv -> ValueEnv
>                 -> Interface
> exportInterface (Module m (Just (Exporting _ es)) _ _) pEnv tcEnv iEnv tyEnv =
>   Interface m imports (precs ++ ds)
>   where tvs = nameSupply
>         imports = map (IImportDecl noPos) (usedModules ds)
>         precs = foldr (infixDecl m pEnv) [] es
>         ds =
>           closeInterface m tcEnv iEnv tvs zeroSet (types ++ values ++ insts)
>         types = foldr (typeDecl m tcEnv tyEnv tvs) [] es
>         values = foldr (valueDecl m tcEnv tyEnv tvs) [] es
>         insts = foldr (uncurry (instDecl m tcEnv tvs)) [] (envToList iEnv)

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

> typeDecl :: ModuleIdent -> TCEnv -> ValueEnv -> [Ident] -> Export -> [IDecl]
>          -> [IDecl]
> typeDecl _ _ _ _ (Export _) ds = ds
> typeDecl m tcEnv tyEnv tvs (ExportTypeWith tc xs) ds =
>   case qualLookupTopEnv tc tcEnv of
>     [DataType _ k cs] ->
>       iTypeDecl IDataDecl m cx' tc tvs n k constrs cs'' : ds
>       where n = kindArity k
>             cx' = guard vis >>
>                   orderContext (map VariableType (take n tvs))
>                                (nub (concat cxs))
>             constrs = guard vis >> cs'
>             (cxs,cs') = unzip (map (constrDecl tcEnv tyEnv tc tvs) cs)
>             cs'' = guard vis >> filter (`notElem` xs) cs
>             vis = not (null xs)
>     [RenamingType _ k c] ->
>       iTypeDecl INewtypeDecl m cx' tc tvs n k nc' cs' : ds
>       where n = kindArity k
>             (cx',nc') = newConstrDecl tcEnv tyEnv tc tvs c
>             cs' = [c | c `notElem` xs]
>     [AliasType _ n k ty] ->
>       iTypeDecl (const . ITypeDecl) m [] tc tvs n k ty' : ds
>       where ty' = fromType tcEnv tvs ty
>     [TypeClass _ k clss fs] ->
>       iClassDecl IClassDecl m tc tvs k clss (methods fs) : ds
>       where methods fs = map (hideDecl (methodDecl tcEnv tyEnv tc tvs) xs) fs
>     _ -> internalError "typeDecl"
>   where hideDecl f xs x = x >>= fmap f . hide xs
>         hide xs x
>           | x `elem` xs = Just x
>           | otherwise = Nothing

> iTypeDecl :: (Position -> [ClassAssert] -> QualIdent -> Maybe KindExpr
>               -> [Ident] -> a)
>           -> ModuleIdent -> [ClassAssert] -> QualIdent -> [Ident] -> Int
>           -> Kind -> a
> iTypeDecl f m cx tc tvs n k = f noPos cx (qualUnqualify m tc) k' (take n tvs)
>   where k' = if k == simpleKind n then Nothing else Just (fromKind k)

> iClassDecl :: (Position -> [ClassAssert] -> QualIdent -> Maybe KindExpr
>                -> Ident -> a)
>            -> ModuleIdent -> QualIdent -> [Ident] -> Kind -> [QualIdent] -> a
> iClassDecl f m cls tvs k clss = f noPos cx (qualUnqualify m cls) k' tv
>   where k' = if k == KindStar then Nothing else Just (fromKind k)
>         tv = head tvs
>         cx =
>           [ClassAssert (qualUnqualify m cls) (VariableType tv) | cls <- clss]

> constrDecl :: TCEnv -> ValueEnv -> QualIdent -> [Ident] -> Ident
>            -> ([ClassAssert],ConstrDecl)
> constrDecl tcEnv tyEnv tc tvs c =
>   (cxL',ConstrDecl noPos (drop (n - n') (take n tvs)) cxR' c (argTypes ty'))
>   where (ConstrInfo n' cxR,ForAll n (QualType cx ty)) =
>           conType (qualifyLike tc c) tyEnv
>         cxL = filter (`notElem` cxR) cx
>         QualTypeExpr cxL' _ = fromQualType tcEnv tvs (QualType cxL ty)
>         QualTypeExpr cxR' ty' = fromQualType tcEnv tvs (QualType cxR ty)

> newConstrDecl :: TCEnv -> ValueEnv -> QualIdent -> [Ident] -> Ident
>               -> ([ClassAssert],NewConstrDecl)
> newConstrDecl tcEnv tyEnv tc tvs c =
>   (cx',NewConstrDecl noPos c (head (argTypes ty')))
>   where ForAll _ ty = snd (conType (qualifyLike tc c) tyEnv)
>         QualTypeExpr cx' ty' = fromQualType tcEnv tvs ty

> methodDecl :: TCEnv -> ValueEnv -> QualIdent -> [Ident] -> Ident
>            -> IMethodDecl
> methodDecl tcEnv tyEnv cls tvs f =
>   IMethodDecl noPos f (fromQualType tcEnv tvs (contextMap tail ty))
>   where ForAll _ ty = funType (qualifyLike cls f) tyEnv

> valueDecl :: ModuleIdent -> TCEnv -> ValueEnv -> [Ident] -> Export -> [IDecl]
>           -> [IDecl]
> valueDecl m tcEnv tyEnv tvs (Export f) ds =
>   IFunctionDecl noPos (qualUnqualify m f) n' (fromQualType tcEnv tvs ty) : ds
>   where n = arity f tyEnv
>         n'
>           | arrowArity (unqualType ty) == n = Nothing
>           | otherwise = Just (toInteger n)
>         ForAll _ ty = funType f tyEnv
> valueDecl _ _ _ _ (ExportTypeWith _ _) ds = ds

> instDecl :: ModuleIdent -> TCEnv -> [Ident] -> CT -> (ModuleIdent,Context)
>          -> [IDecl] -> [IDecl]
> instDecl m tcEnv tvs (CT cls tc) (m',cx) ds
>   | mIdent m cls /= m' && (isPrimTypeId tc || mIdent m tc /= m') =
>       iInstDecl m tcEnv tvs (CT cls tc) (m',cx) : ds
>   | otherwise = ds
>   where mIdent m = fromMaybe m . fst . splitQualIdent 

> iInstDecl :: ModuleIdent -> TCEnv -> [Ident] -> CT -> (ModuleIdent,Context)
>           -> IDecl
> iInstDecl m tcEnv tvs (CT cls tc) (m',cx) =
>   IInstanceDecl noPos cx' (qualUnqualify m cls) ty' m''
>   where m'' = if m == m' then Nothing else Just m'
>         QualTypeExpr cx' ty' = fromQualType tcEnv tvs $
>           QualType cx (applyType (TypeConstructor tc) tvs')
>         n = kindArity (constrKind tc tcEnv) - kindArity (classKind cls tcEnv)
>         tvs' = take n (map TypeVariable [0..])

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
module A where { data T = T; }
module B(T(..)) where { import A; }
module C where { import B; x = T; }
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
>   modules (IInfixDecl _ _ _ op) = modules op
>   modules (HidingDataDecl _ tc _ _) = modules tc
>   modules (IDataDecl _ cx tc _ _ cs _) = modules cx . modules tc . modules cs
>   modules (INewtypeDecl _ cx tc _ _ nc _) =
>     modules cx . modules tc . modules nc
>   modules (ITypeDecl _ tc _ _ ty) = modules tc . modules ty
>   modules (HidingClassDecl _ cx cls _ _) = modules cx . modules cls
>   modules (IClassDecl _ cx cls _ _ ds) = modules cx . modules cls . modules ds
>   modules (IInstanceDecl _ cx cls ty m) =
>      modules cx . modules cls . modules ty . maybe id (:) m
>   modules (IFunctionDecl _ f _ ty) = modules f . modules ty

> instance HasModule ConstrDecl where
>   modules (ConstrDecl _ _ cx _ tys) = modules cx . modules tys
>   modules (ConOpDecl _ _ cx ty1 _ ty2) =
>     modules cx . modules ty1 . modules ty2

> instance HasModule NewConstrDecl where
>   modules (NewConstrDecl _ _ ty) = modules ty

> instance HasModule IMethodDecl where
>   modules (IMethodDecl _ _ ty) = modules ty

> instance HasModule QualTypeExpr where
>   modules (QualTypeExpr cx ty) = modules cx . modules ty

> instance HasModule ClassAssert where
>   modules (ClassAssert cls ty) = modules cls . modules ty

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
After an initial interface has been computed from the list of exported
types and classes, the compiler adds hidden (data) type and class
declarations to the interface for all types and classes which are used
in the interface but not exported from it. For types declared in the
current module, hidden type declarations are necessary in order to
distinguish type constructors and type variables in the interface.
Furthermore, by including hidden types and classes in interfaces the
compiler can check them without loading the imported modules. Besides
hidden type and class declarations, the compiler also adds the
necessary instance declarations to the interface. Since class and
instance declarations added to an interface can require the inclusion
of further classes by their respective contexts, closing an interface
is implemented as a fix-point computation which starts from the
initial interface.

The Haskell report requires that ``all instances in scope within a
module are \emph{always} exported'' (\cite{PeytonJones03:Haskell},
Sect.~5.4). Thus, it seems the compiler should dump the whole instance
environment to the module's interface. Fortunately, it is not really
necessary to include all instance declarations that are in scope in a
module in its interface. Since in order to use an instance both the
instance's class and type must be in scope (eventually implicitly due
to declarations using the class and type, respectively), an instance
that is defined in the same module as its class or its type is
exported only if the class or type occurs in the interface as well.
Only instances that are defined in a module that is different from
both the modules defining its class and its type are always exported
when they are in scope. This leads to smaller interfaces which can be
loaded more quickly by the compiler and are easier to understand for
the user.

More formally, an instance $M_1.C\;(M_2.T\,u_1 \dots u_n)$ defined in
module $M_3$ is exported from module $M_4$ if either
\begin{enumerate}
  \item $M_1=M_3 \land M_1.C \in \emph{intf}(M_4)$, or
  \item $M_1\not=M_3 \land M_2=M_3 \land M_2.T \in \emph{intf}(M_4)$, or
  \item $M_1\not=M_3 \land M_2\not=M_3$.
\end{enumerate}
The condition $M_1\not=M_3$ in the second alternative takes care to
always export an instance of a class and a type which are defined in
the same module together with the class only. As a special case, if
the class and the type are both defined in the current module, the
instance is exported only if both appear in the interface, i.e., we
impose the additional restriction
\begin{displaymath}
  M_1\not=M_4 \lor M_2\not=M_4 \lor M_3\not=M_4 \lor (M_1.C \in
  \emph{intf}(M_4) \land M_2.T \in \emph{intf}(M_4)) .
\end{displaymath}
Obviously, this restriction affects only the first alternative, since
if $M_1\not=M_3$ at least one of the conditions $M_1\not=M_4$ and
$M_3\not=M_4$ is true. Taking the additional restriction into account,
the first alternative becomes
\begin{enumerate}
  \item[1'.] $M_1=M_3 \land M_1.C \in \emph{intf}(M_4) \land
    (M_1\not=M_4 \lor M_2\not=M_4 \lor M_2.T \in \emph{intf}(M_4))$.
\end{enumerate}

While computing the closure of an interface, the first condition is
considered for all classes that are part of the interface, and the
first and the second condition are considered for all types that are
part of the interface. Instances for which the third condition holds
are already included in the initial interface by \texttt{instDecls}
above. If $T$ is one of the primitive type constructors \texttt{()},
\texttt{[]}, \texttt{(->)}, or a tuple type constructor, we stipulate
$M_2\not=M_3$.

Note that we do not categorize type synonym declarations as type
declarations in \texttt{declIs} below because instances can be
declared only for data and renaming types and therefore there is no
point looking for any instances of the type in the instance
environment.
\begin{verbatim}

> data DeclIs =
>   IsOther | IsType QualIdent | IsClass QualIdent | IsInst CT deriving (Eq,Ord)

> closeInterface :: ModuleIdent -> TCEnv -> InstEnv -> [Ident] -> Set DeclIs
>                -> [IDecl] -> [IDecl]
> closeInterface _ _ _ _ _ [] = []
> closeInterface m tcEnv iEnv tvs ds' (d:ds)
>   | d' == IsOther = d : closeInterface m tcEnv iEnv tvs ds' (ds ++ ds'')
>   | d' `elemSet` ds' = closeInterface m tcEnv iEnv tvs ds' ds
>   | otherwise =
>       d : closeInterface m tcEnv iEnv tvs (d' `addToSet` ds') (ds ++ ds'')
>   where d' = declIs m d
>         ds'' =
>           map (hiddenTypeDecl m tcEnv tvs)
>               (filter (not . isPrimTypeId) (usedTypes d [])) ++
>           instances m tcEnv iEnv tvs ds' d'

> declIs :: ModuleIdent -> IDecl -> DeclIs
> declIs _ (IInfixDecl _ _ _ _) = IsOther
> declIs m (HidingDataDecl _ tc _ _) = IsType (qualQualify m tc)
> declIs m (IDataDecl _ _ tc _ _ _ _) = IsType (qualQualify m tc)
> declIs m (INewtypeDecl _ _ tc _ _ _ _) = IsType (qualQualify m tc)
> declIs _ (ITypeDecl _ _ _ _ _) = IsOther {-sic!-}
> declIs m (HidingClassDecl _ _ cls _ _) = IsClass (qualQualify m cls)
> declIs m (IClassDecl _ _ cls _ _ _) = IsClass (qualQualify m cls)
> declIs m (IInstanceDecl _ _ cls ty _) = IsInst (CT cls' tc')
>   where cls' = qualQualify m cls 
>         tc' = if isPrimTypeId tc then tc else qualQualify m tc
>         tc = typeConstr ty
> declIs _ (IFunctionDecl _ _ _ _) = IsOther

> instances :: ModuleIdent -> TCEnv -> InstEnv -> [Ident] -> Set DeclIs
>           -> DeclIs -> [IDecl]
> instances _ _ _ _ _ IsOther = []
> instances m tcEnv iEnv tvs ds' (IsType tc) =
>   [iInstDecl m tcEnv tvs (CT cls tc) (m',cx)
>   | (CT cls tc',(m',cx)) <- envToList iEnv,
>     tc == tc',
>     if mIdent m cls == m'
>       then IsClass cls `elemSet` ds'
>       else mIdent m tc == m']
>   where mIdent m = fromMaybe m . fst . splitQualIdent
> instances m tcEnv iEnv tvs ds' (IsClass cls) =
>   [iInstDecl m tcEnv tvs (CT cls tc) (m',cx)
>   | (CT cls' tc,(m',cx)) <- envToList iEnv,
>     cls == cls',
>     mIdent m cls == m',
>     m /= m' || isPrimTypeId tc || mIdent m tc /= m || IsType tc `elemSet` ds']
>   where mIdent m = fromMaybe m . fst . splitQualIdent
> instances _ _ _ _ _ (IsInst _) = []

> hiddenTypeDecl :: ModuleIdent -> TCEnv -> [Ident] -> QualIdent -> IDecl
> hiddenTypeDecl m tcEnv tvs tc =
>   case qualLookupTopEnv (qualQualify m tc) tcEnv of
>     [DataType _ k _] ->
>       iTypeDecl hidingDataDecl m [] tc tvs (kindArity k) k undefined
>     [RenamingType _ k _] ->
>       iTypeDecl hidingDataDecl m [] tc tvs (kindArity k) k undefined
>     [TypeClass _ k clss _] -> iClassDecl HidingClassDecl m tc tvs k clss
>     _ -> internalError "hiddenTypeDecl"
>   where hidingDataDecl p _ tc k tvs _ = HidingDataDecl p tc k tvs

> class HasType a where
>   usedTypes :: a -> [QualIdent] -> [QualIdent]

> instance HasType a => HasType (Maybe a) where
>   usedTypes = maybe id usedTypes

> instance HasType a => HasType [a] where
>   usedTypes xs tcs = foldr usedTypes tcs xs

> instance HasType IDecl where
>   usedTypes (IInfixDecl _ _ _ _) = id
>   usedTypes (HidingDataDecl _ _ _ _) = id
>   usedTypes (IDataDecl _ cx _ _ _ cs _) = usedTypes cx . usedTypes cs
>   usedTypes (INewtypeDecl _ cx _ _ _ nc _) = usedTypes cx . usedTypes nc
>   usedTypes (ITypeDecl _ _ _ _ ty) = usedTypes ty
>   usedTypes (HidingClassDecl _ cx _ _ _) = usedTypes cx
>   usedTypes (IClassDecl _ cx _ _ _ ds) = usedTypes cx . usedTypes ds
>   usedTypes (IInstanceDecl _ cx cls ty _) =
>     usedTypes cx . (cls :) . usedTypes ty
>   usedTypes (IFunctionDecl _ _ _ ty) = usedTypes ty

> instance HasType ConstrDecl where
>   usedTypes (ConstrDecl _ _ cx _ tys) = usedTypes cx . usedTypes tys
>   usedTypes (ConOpDecl _ _ cx ty1 _ ty2) =
>     usedTypes cx . usedTypes ty1 . usedTypes ty2

> instance HasType NewConstrDecl where
>   usedTypes (NewConstrDecl _ _ ty) = usedTypes ty

> instance HasType IMethodDecl where
>   usedTypes (IMethodDecl _ _ ty) = usedTypes ty

> instance HasType QualTypeExpr where
>   usedTypes (QualTypeExpr cx ty) = usedTypes cx . usedTypes ty

> instance HasType ClassAssert where
>   usedTypes (ClassAssert cls ty) = (cls :) . usedTypes ty

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

> orderContext :: [TypeExpr] -> [ClassAssert] -> [ClassAssert]
> orderContext [] _ = []
> orderContext (ty:tys) cx = cx' ++ orderContext tys cx''
>   where (cx',cx'') = partition (\(ClassAssert _ ty') -> ty == root ty') cx
>         root (ApplyType ty _) = root ty
>         root ty = ty

> argTypes :: TypeExpr -> [TypeExpr]
> argTypes (ArrowType ty1 ty2) = ty1 : argTypes ty2
> argTypes _ = []

\end{verbatim}
