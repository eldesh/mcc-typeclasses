% -*- LaTeX -*-
% $Id: Exports.lhs 3300 2019-08-31 10:23:56Z wlux $
%
% Copyright (c) 2000-2019, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Exports.lhs}
\section{Creating Interfaces}\label{sec:exports}
After checking a module, the compiler generates the interface's
declarations from the list of exported types and values. If an entity
is imported from another module, its name is qualified with the name
of the module containing its definition. Instances are exported
together with their classes and types as explained below.

Data types and renaming types whose constructors and field labels are
not exported are exported as abstract types, i.e., their constructors
do not appear in the interface. If only some constructors or field
labels of a type are not exported all constructors appear in the
interface, but a pragma marks the constructors and field labels which
are not exported as hidden to prevent their use in user code. A
special case is made for the \verb|:%| constructor of type
\texttt{Ratio.Ratio} to appear as hidden data constructor in the
interface even though the type itself is exported as an abstract type.
This is necessary because the compiler uses the constructor internally
to define rational number constants  (cf.\ Sect.~\ref{sec:desugar}
and~\ref{sec:flatcase}).

\textbf{Attention:} The compiler assumes that the environments passed
to \texttt{exportInterface} reflect the types of the module's entities
after type inference. However, the source code module passed to
\texttt{exportInterface} must reflect the module's code \emph{after}
applying all source code transformations to the program so that
correct arity annotations are written to the interface.
\begin{verbatim}

> module Exports(exportInterface) where
> import Base
> import Curry
> import CurryUtils
> import Env
> import InstInfo
> import IntfQual
> import Kinds
> import KindTrans
> import List
> import Maybe
> import PrecInfo
> import PredefIdent
> import Set
> import TopEnv
> import Types
> import TypeInfo
> import TypeTrans
> import ValueInfo

> exportInterface :: Module a -> PEnv -> TCEnv -> InstEnv -> ValueEnv
>                 -> Interface
> exportInterface (Module m (Just (Exporting _ es)) _ ds) pEnv tcEnv iEnv tyEnv =
>   Interface m imports (unqualIntf m (precs ++ ds''))
>   where aEnv = bindArities m ds
>         tcs = foldr definedType [] ds''
>         tcs' = [tc | Just tc <- map (localIdent m) tcs]
>         tvs = filter (`notElem` tcs') nameSupply
>         imports = map (IImportDecl noPos) (filter (m /=) (usedModules ds''))
>         precs = foldr (infixDecl pEnv) [] es
>         ds' = types ++ values ++ insts
>         ds'' = closeInterface m tcEnv iEnv aEnv tvs zeroSet ds'
>         types = foldr (typeDecl tcEnv aEnv tyEnv tvs) [] es
>         values = foldr (valueDecl aEnv tyEnv tvs) [] es
>         insts = foldr (uncurry (instDecl tcEnv aEnv tvs)) [] (envToList iEnv)

> infixDecl :: PEnv -> Export -> [IDecl] -> [IDecl]
> infixDecl pEnv (Export f) ds = iInfixDecl pEnv f ds
> infixDecl pEnv (ExportTypeWith tc cs) ds =
>   foldr (iInfixDecl pEnv . qualifyLike tc) ds cs

> iInfixDecl :: PEnv -> QualIdent -> [IDecl] -> [IDecl]
> iInfixDecl pEnv op ds =
>   case qualLookupTopEnv op pEnv of
>     [] -> ds
>     [PrecInfo _ (OpPrec fix pr)] -> IInfixDecl noPos fix pr op : ds
>     _ -> internalError "infixDecl"

> typeDecl :: TCEnv -> ArityEnv -> ValueEnv -> [Ident] -> Export -> [IDecl]
>          -> [IDecl]
> typeDecl _ _ _ _ (Export _) ds = ds
> typeDecl tcEnv aEnv tyEnv tvs (ExportTypeWith tc xs) ds =
>   case qualLookupTopEnv tc tcEnv of
>     [DataType _ k cs]
>       | null xs && tc /= qRatioId ->
>           iTypeDecl IDataDecl [] tc tvs n k [] [] : ds
>       | otherwise -> iTypeDecl IDataDecl cx' tc tvs n k cs' xs' : ds
>       where n = kindArity k
>             xs' = filter (`notElem` xs) (cs ++ ls)
>             QualTypeExpr cx' _ = fromQualType tvs ty'
>             ty' = canonType (qualInstType (nub (concat cxs)) tc n)
>             (cxs,cs') = unzip (map (constrDecl tyEnv xs tc tvs) cs)
>             ls = nub (concatMap labels cs')
>     [RenamingType _ k c]
>       | null xs -> iTypeDecl IDataDecl [] tc tvs n k [] [] : ds
>       | otherwise -> iTypeDecl INewtypeDecl cx tc tvs n k nc xs' : ds
>       where n = kindArity k
>             (cx,nc) = newConstrDecl tyEnv xs tc tvs c
>             xs' = [c | c `notElem` xs]
>     [AliasType _ n k ty] ->
>       iTypeDecl (const . ITypeDecl) [] tc tvs n k (fromType tvs ty) : ds
>     [TypeClass _ k clss fs] ->
>       iClassDecl IClassDecl tc tvs k clss methods fs' : ds
>       where methods = map (methodDecl aEnv tyEnv tc tvs) fs
>             fs' = filter (`notElem` xs) (map fst fs)
>     _ -> internalError "typeDecl"

> iTypeDecl :: (Position -> [ClassAssert] -> QualIdent -> Maybe KindExpr
>               -> [Ident] -> a)
>           -> [ClassAssert] -> QualIdent -> [Ident] -> Int -> Kind -> a
> iTypeDecl f cx tc tvs n k = f noPos cx tc k' (take n tvs)
>   where k' = if k == simpleKind n then Nothing else Just (fromKind k)

> iClassDecl :: (Position -> [ClassAssert] -> QualIdent -> Maybe KindExpr
>                -> Ident -> a)
>            -> QualIdent -> [Ident] -> Kind -> [QualIdent] -> a
> iClassDecl f cls tvs k clss = f noPos cx cls k' tv
>   where k' = if k == KindStar then Nothing else Just (fromKind k)
>         tv = head tvs
>         cx = [ClassAssert cls (VariableType tv) | cls <- clss]

> constrDecl :: ValueEnv -> [Ident] -> QualIdent -> [Ident] -> Ident
>            -> (Context,ConstrDecl)
> constrDecl tyEnv xs tc tvs c
>   | any (`elem` xs) ls = (cxL,RecordDecl noPos evs cxR' c fs)
>   | otherwise = (cxL,ConstrDecl noPos evs cxR' c tys)
>   where evs = drop (n - n') (take n tvs)
>         (ls,ConstrInfo n' cxR,ForAll n (QualType cx ty)) =
>           conType (qualifyLike tc c) tyEnv
>         cxL = filter (`notElem` cxR) cx
>         QualTypeExpr cxR' ty' = fromQualType tvs (QualType cxR ty)
>         tys = argTypes ty'
>         fs = zipWith (FieldDecl noPos . return) ls tys

> newConstrDecl :: ValueEnv -> [Ident] -> QualIdent -> [Ident] -> Ident
>               -> ([ClassAssert],NewConstrDecl)
> newConstrDecl tyEnv xs tc tvs c
>   | l `elem` xs = (cx',NewRecordDecl noPos c l ty'')
>   | otherwise = (cx',NewConstrDecl noPos c ty'')
>   where (l:_,_,ForAll _ ty) = conType (qualifyLike tc c) tyEnv
>         QualTypeExpr cx' ty' = fromQualType tvs ty
>         ty'' = head (argTypes ty')

> methodDecl :: ArityEnv -> ValueEnv -> QualIdent -> [Ident] -> (Ident,Int)
>            -> IMethodDecl
> methodDecl aEnv tyEnv cls tvs (f,n) =
>   IMethodDecl noPos f n' (fromQualType tvs (contextMap tail ty))
>   where n' = arityAnnot (qualifyLike cls (dfltMethodId f)) n 0 aEnv
>         ForAll _ ty = funType (qualifyLike cls f) tyEnv

> valueDecl :: ArityEnv -> ValueEnv -> [Ident] -> Export -> [IDecl] -> [IDecl]
> valueDecl aEnv tyEnv tvs (Export f) ds =
>   IFunctionDecl noPos f n (fromQualType tvs ty) : ds
>   where n = arityAnnot f (arity f tyEnv) (arrowArity (unqualType ty)) aEnv
>         ForAll _ ty = funType f tyEnv
> valueDecl _ _ _ (ExportTypeWith _ _) ds = ds

> instDecl :: TCEnv -> ArityEnv -> [Ident] -> CT -> InstInfo -> [IDecl]
>          -> [IDecl]
> instDecl tcEnv aEnv tvs (CT cls tc) (m,cx,fs) ds
>   | fst (splitQualIdent cls) /= Just m && fst (splitQualIdent tc) /= Just m =
>       iInstDecl tcEnv aEnv tvs (CT cls tc) (m,cx,fs) : ds
>   | otherwise = ds

> iInstDecl :: TCEnv -> ArityEnv -> [Ident] -> CT -> InstInfo -> IDecl
> iInstDecl tcEnv aEnv tvs (CT cls tc) (m,cx,fs) =
>   IInstanceDecl noPos cx' cls ty' (Just m) [(f,n) | (f,Just n) <- fs']
>   where QualTypeExpr cx' ty' = fromQualType tvs (qualInstType cx tc n)
>         n = kindArity (constrKind tc tcEnv) - kindArity (classKind cls tcEnv)
>         fs' = [(f,arityAnnot (qInstMethodId m tc f) n 0 aEnv) | (f,n) <- fs]
>         qInstMethodId m tc f = qualifyWith m (instMethodId tc f)

> arityAnnot :: QualIdent -> Int -> Int -> ArityEnv -> Maybe Integer
> arityAnnot f n n0 aEnv = if n' == n0 then Nothing else Just (toInteger n')
>   where n' = fromMaybe n (lookupEnv f aEnv)

\end{verbatim}
Simplification can change the arity of an exported function defined in
the current module via $\eta$-expansion (cf.\ 
Sect.~\ref{sec:simplify}). In order to generate correct arity
annotations, the compiler collects the arities of all user defined
functions at the top-level and in the class and instance declarations
of the transformed code in an auxiliary environment. Note that we
ignore foreign function declarations here because their arities are
fixed and cannot be changed by program transformations. When adding
the arities of default type class and instance methods, we must remove
the unique key added during renaming. Furthermore, we prefix default
and instance method identifiers with an anonymous identifier and the
name of the instance's type, respectively. This is necessary for
default method implementations so that their arities are not confused
with that of a method (stub) if a method is exported without its
class, i.e., like a top-level function, and for instance methods to
avoid name conflicts between methods of different instances of the
same class.
\begin{verbatim}

> type ArityEnv = Env QualIdent Int

> bindArities :: ModuleIdent -> [TopDecl a] -> ArityEnv
> bindArities m ds = foldr bindArity emptyEnv (concatMap functions ds)
>   where bindArity (f,eqs) = bindEnv (qualifyWith m f) (eqnArity (head eqs))

> functions :: TopDecl a -> [(Ident,[Equation a])]
> functions (DataDecl _ _ _ _ _ _) = []
> functions (NewtypeDecl _ _ _ _ _ _) = []
> functions (TypeDecl _ _ _ _) = []
> functions (ClassDecl _ _ _ _ ds) =
>   [(dfltMethodId (unRenameIdent f),eqs) | FunctionDecl _ _ f eqs <- ds]
> functions (InstanceDecl _ _ _ ty ds) =
>   [(instMethodId tc (unRenameIdent f),eqs) | FunctionDecl _ _ f eqs <- ds]
>   where tc = typeConstr ty
> functions (DefaultDecl _ _) = []
> functions (BlockDecl d) =
>   case d of
>     FunctionDecl _ _ f eqs -> [(f,eqs)]
>     _ -> []

> dfltMethodId  :: Ident -> Ident
> dfltMethodId = instMethodId (qualify anonId)

> instMethodId :: QualIdent -> Ident -> Ident
> instMethodId tc f = mkIdent (qualName tc ++ '.' : name f)

\end{verbatim}
The compiler determines the list of imported modules from the set of
module qualifiers that are used in the interface. Note that the list
of modules returned from \texttt{usedModules} is not necessarily a
subset of the union of the current module and the modules that were
imported into it. This will happen when an imported module reexports
entities from another module. E.g., given the three modules
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
>   modules (IClassDecl _ cx cls _ _ ds _) =
>     modules cx . modules cls . modules ds
>   modules (IInstanceDecl _ cx cls ty m _) =
>      modules cx . modules cls . modules ty . maybe id (:) m
>   modules (IFunctionDecl _ f _ ty) = modules f . modules ty

> instance HasModule ConstrDecl where
>   modules (ConstrDecl _ _ cx _ tys) = modules cx . modules tys
>   modules (ConOpDecl _ _ cx ty1 _ ty2) =
>     modules cx . modules ty1 . modules ty2
>   modules (RecordDecl _ _ cx _ fs) = modules cx . modules fs

> instance HasModule FieldDecl where
>   modules (FieldDecl _ _ ty) = modules ty

> instance HasModule NewConstrDecl where
>   modules (NewConstrDecl _ _ ty) = modules ty
>   modules (NewRecordDecl _ _ _ ty) = modules ty

> instance HasModule IMethodDecl where
>   modules (IMethodDecl _ _ _ ty) = modules ty

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
The condition $M_1\not=M_3$ in the second alternative takes care of
exporting an instance of a class and a type defined in the same module
together with the class only. As a special case, if the class and the
type are both defined in the current module, the instance is exported
only if both appear in the interface, i.e., we impose the additional
restriction
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

> closeInterface :: ModuleIdent -> TCEnv -> InstEnv -> ArityEnv -> [Ident]
>                -> Set DeclIs -> [IDecl] -> [IDecl]
> closeInterface _ _ _ _ _ _ [] = []
> closeInterface m tcEnv iEnv aEnv tvs ds' (d:ds)
>   | d' == IsOther =
>       d : closeInterface m tcEnv iEnv aEnv tvs ds' (ds ++ ds'')
>   | d' `elemSet` ds' = closeInterface m tcEnv iEnv aEnv tvs ds' ds
>   | otherwise =
>       d : closeInterface m tcEnv iEnv aEnv tvs (d' `addToSet` ds') (ds ++ ds'')
>   where d' = declIs d
>         ds'' =
>           map (hiddenTypeDecl tcEnv tvs)
>               (filter (not . isPrimTypeId . unqualify) (usedTypes d [])) ++
>           instances m tcEnv iEnv aEnv tvs ds' d'

> declIs :: IDecl -> DeclIs
> declIs (IInfixDecl _ _ _ _) = IsOther
> declIs (HidingDataDecl _ tc _ _) = IsType tc
> declIs (IDataDecl _ _ tc _ _ _ _) = IsType tc
> declIs (INewtypeDecl _ _ tc _ _ _ _) = IsType tc
> declIs (ITypeDecl _ _ _ _ _) = IsOther {-sic!-}
> declIs (HidingClassDecl _ _ cls _ _) = IsClass cls
> declIs (IClassDecl _ _ cls _ _ _ _) = IsClass cls
> declIs (IInstanceDecl _ _ cls ty _ _) = IsInst (CT cls (typeConstr ty))
> declIs (IFunctionDecl _ _ _ _) = IsOther

> definedType :: IDecl -> [QualIdent] -> [QualIdent]
> definedType (IInfixDecl _ _ _ _) tcs = tcs
> definedType (HidingDataDecl _ tc _ _) tcs = tc : tcs
> definedType (IDataDecl _ _ tc _ _ _ _) tcs = tc : tcs
> definedType (INewtypeDecl _ _ tc _ _ _ _) tcs = tc : tcs
> definedType (ITypeDecl _ tc _ _ _) tcs = tc : tcs
> definedType (HidingClassDecl _ _ cls _ _) tcs = cls : tcs
> definedType (IClassDecl _ _ cls _ _ _ _) tcs = cls : tcs
> definedType (IInstanceDecl _ _ _ _ _ _) tcs = tcs
> definedType (IFunctionDecl _ _ _ _) tcs = tcs

> instances :: ModuleIdent -> TCEnv -> InstEnv -> ArityEnv -> [Ident]
>           -> Set DeclIs -> DeclIs -> [IDecl]
> instances _ _ _ _ _ _ IsOther = []
> instances _ tcEnv iEnv aEnv tvs ds' (IsType tc) =
>   [iInstDecl tcEnv aEnv tvs (CT cls tc) (m',cx,fs)
>   | (CT cls tc',(m',cx,fs)) <- envToList iEnv,
>     tc == tc',
>     if fst (splitQualIdent cls) == Just m'
>       then IsClass cls `elemSet` ds'
>       else fst (splitQualIdent tc) == Just m']
> instances m tcEnv iEnv aEnv tvs ds' (IsClass cls) =
>   [iInstDecl tcEnv aEnv tvs (CT cls tc) (m',cx,fs)
>   | (CT cls' tc,(m',cx,fs)) <- envToList iEnv,
>     cls == cls',
>     fst (splitQualIdent cls) == Just m',
>     m /= m' || isPrimTypeId (unqualify tc)
>             || fst (splitQualIdent tc) /= Just m
>             || IsType tc `elemSet` ds']
> instances _ _ _ _ _ _ (IsInst _) = []

> hiddenTypeDecl :: TCEnv -> [Ident] -> QualIdent -> IDecl
> hiddenTypeDecl tcEnv tvs tc =
>   case qualLookupTopEnv tc tcEnv of
>     [DataType _ k _] ->
>       iTypeDecl hidingDataDecl [] tc tvs (kindArity k) k undefined
>     [RenamingType _ k _] ->
>       iTypeDecl hidingDataDecl [] tc tvs (kindArity k) k undefined
>     [TypeClass _ k clss _] -> iClassDecl HidingClassDecl tc tvs k clss
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
>   usedTypes (IClassDecl _ cx _ _ _ ds _) = usedTypes cx . usedTypes ds
>   usedTypes (IInstanceDecl _ cx cls ty _ _) =
>     usedTypes cx . (cls :) . usedTypes ty
>   usedTypes (IFunctionDecl _ _ _ ty) = usedTypes ty

> instance HasType ConstrDecl where
>   usedTypes (ConstrDecl _ _ cx _ tys) = usedTypes cx . usedTypes tys
>   usedTypes (ConOpDecl _ _ cx ty1 _ ty2) =
>     usedTypes cx . usedTypes ty1 . usedTypes ty2
>   usedTypes (RecordDecl _ _ cx _ fs) = usedTypes cx . usedTypes fs

> instance HasType FieldDecl where
>   usedTypes (FieldDecl _ _ ty) = usedTypes ty

> instance HasType NewConstrDecl where
>   usedTypes (NewConstrDecl _ _ ty) = usedTypes ty
>   usedTypes (NewRecordDecl _ _ _ ty) = usedTypes ty

> instance HasType IMethodDecl where
>   usedTypes (IMethodDecl _ _ _ ty) = usedTypes ty

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

> argTypes :: TypeExpr -> [TypeExpr]
> argTypes (ArrowType ty1 ty2) = ty1 : argTypes ty2
> argTypes _ = []

> qualInstType :: Context -> QualIdent -> Int -> QualType
> qualInstType cx tc n =
>   QualType cx (applyType (TypeConstructor tc) (map TypeVariable [0..n-1]))

\end{verbatim}
