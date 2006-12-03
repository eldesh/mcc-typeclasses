% -*- LaTeX -*-
% $Id: DictTrans.lhs 2035 2006-12-03 10:24:34Z wlux $
%
% Copyright (c) 2006, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{DictTrans.lhs}
\section{Introducing Dictionaries}\label{sec:dict-trans}
For the implementation of type classes, we follow the common approach
to use dictionaries~\cite{PetersonJones93:TypeClasses}. For every type
predicate in the context of a function's type we introduce an implicit
dictionary argument. The dictionaries themselves are derived from the
type class and instance declarations in the module.

This module applies the necessary transformations to the source code
of a module. Note that all identifiers are expected to be qualified
properly, but the source code has not been desugared yet. In
particular, the compiler \emph{must not} remove newtype constructors
from the source code before invoking the functions from this module.

\ToDo{It would be useful if part of the desugaring that is performed
  in module \texttt{Desugar} were performed before the transformations
  from this module.}
\begin{verbatim}

> module DictTrans(dictTransModule, dictTransInterface, dictTransGoal) where
> import Base
> import Combined
> import Env
> import List
> import Maybe
> import Monad
> import TopEnv
> import TypeSubst
> import TypeTrans
> import Typing

\end{verbatim}
In order to generate unique names for the implicit dictionary
arguments and add their types to the type environment, we use a nested
state monad.
\begin{verbatim}

> type DictState a = StateT ValueEnv (StateT Int Id) a

> run :: DictState a -> ValueEnv -> a
> run m tyEnv = runSt (callSt m tyEnv) 1

\end{verbatim}
The introduction of dictionaries is divided into six different tasks:
\begin{enumerate}
\item Introduce a dictionary type for each class defined in the
  current module,
\item introduce a stub function for each type class method declared in
  the current module,
\item lift all default method implementations to the top-level,
\item introduce a global function for each instance declaration in the
  current module that returns an appropriate dictionary,
\item add dictionary arguments to the left hand sides of all equations
  and update the function types accordingly, and
\item add dictionary argument expressions to every application of a
  function with a non-trivial context.
\end{enumerate}
\begin{verbatim}

> doTrans :: (ModuleIdent -> TCEnv -> ValueEnv -> a -> DictState b) -> TCEnv
>         -> InstEnv -> ValueEnv -> ModuleIdent -> a -> (TCEnv,ValueEnv,b)
> doTrans f tcEnv iEnv tyEnv m x =
>   run (f m tcEnv tyEnv' x >>= \x' -> fetchSt >>= \tyEnv'' ->
>        return (bindDictTypes tcEnv,tyEnv'',x'))
>       (bindDictConstrs m tcEnv $ bindInstFuns tcEnv iEnv $ rebindFuns tyEnv')
>   where tyEnv' = bindClassMethods m tcEnv tyEnv

> dictTransModule :: TCEnv -> InstEnv -> ValueEnv -> Module Type
>                 -> (TCEnv,ValueEnv,Module Type)
> dictTransModule tcEnv iEnv tyEnv (Module m es is ds) =
>   doTrans transModule tcEnv iEnv tyEnv m ds
>   where transModule m tcEnv tyEnv ds =
>           do
>             ds' <- mapM (dictTransTopDecl m tcEnv iEnv tyEnv)
>                         (ds ++ concatMap (defaultMethodDecls tyEnv) ds)
>             dss <- mapM (methodStubs m tcEnv tyEnv) ds
>             return (Module m es is (ds' ++ concat dss))

> dictTransTopDecl :: ModuleIdent -> TCEnv -> InstEnv -> ValueEnv
>                  -> TopDecl Type -> DictState (TopDecl Type)
> dictTransTopDecl _ _ _ _ (DataDecl p _ tc tvs cs) =
>   return (DataDecl p [] tc tvs cs)
> dictTransTopDecl _ _ _ _ (NewtypeDecl p _ tc tvs nc) =
>   return (NewtypeDecl p [] tc tvs nc)
> dictTransTopDecl _ _ _ _ (TypeDecl p tc tvs ty) =
>   return (TypeDecl p tc tvs ty)
> dictTransTopDecl _ _ _ _ (ClassDecl p _ cls tv ds) =
>   return (dictDecl p cls tv ds)
> dictTransTopDecl m tcEnv iEnv tyEnv (InstanceDecl p cx cls ty ds) =
>   instDecl m tcEnv iEnv tyEnv p cx cls ty ds
> dictTransTopDecl m _ iEnv tyEnv (BlockDecl d) =
>   liftM BlockDecl (dictTrans m iEnv tyEnv emptyEnv d)

> dictTransGoal :: TCEnv -> InstEnv -> ValueEnv -> ModuleIdent -> Goal Type
>               -> (TCEnv,ValueEnv,Goal Type)
> dictTransGoal tcEnv iEnv tyEnv m g = doTrans transGoal tcEnv iEnv tyEnv m g
>   where transGoal m tcEnv tyEnv = dictTrans m iEnv tyEnv emptyEnv

\end{verbatim}
Besides the source code definitions, the compiler must also transform
the imported interface modules because their declarations are used to
supply the appropriate environment for the abstract machine code
generator.
\begin{verbatim}

> dictTransInterface :: Interface -> Interface
> dictTransInterface (Interface m is ds) =
>   Interface m is (map (dictTransIntfDecl m) (ds ++ dss))
>   where dss = concatMap (intfMethodStubs m) ds ++
>               concatMap (intfDefaultMethodDecls m) ds

> dictTransIntfDecl :: ModuleIdent -> IDecl -> IDecl
> dictTransIntfDecl _ (IInfixDecl p fix pr op) = IInfixDecl p fix pr op
> dictTransIntfDecl _ (HidingDataDecl p tc tvs) = HidingDataDecl p tc tvs
> dictTransIntfDecl _ (IDataDecl p _ tc tvs cs) = IDataDecl p [] tc tvs cs
> dictTransIntfDecl _ (INewtypeDecl p _ tc tvs nc) = INewtypeDecl p [] tc tvs nc
> dictTransIntfDecl _ (ITypeDecl p tc tvs ty) = ITypeDecl p tc tvs ty
> dictTransIntfDecl _ (HidingClassDecl p _ cls tv) = dictIDecl p cls tv Nothing
> dictTransIntfDecl _ (IClassDecl p _ cls tv ds) = dictIDecl p cls tv (Just ds)
> dictTransIntfDecl m (IInstanceDecl p cx cls ty) = instIDecl m p cx cls ty
> dictTransIntfDecl m (IFunctionDecl p f ty) =
>   IFunctionDecl p f (fromTransType m (transformType (toQualType m [] ty)))

> fromTransType :: ModuleIdent -> Type -> QualTypeExpr
> fromTransType m = QualTypeExpr [] . fromType m

\end{verbatim}
\paragraph{Dictionary Types}
For every type class declaration
\begin{displaymath}
  \mbox{\texttt{class} $C$ $a$ \texttt{where} \texttt{\lb} $f_1$
    \texttt{::} $\tau_1$\texttt{;} \dots\texttt{;} $f_n$ \texttt{::}
    $\tau_n$ \texttt{\rb}}
\end{displaymath}
a dictionary type declaration
\begin{displaymath}
  \mbox{\texttt{data} $T$ $a$ \texttt{=} $C'$ $\tau_1$ $\dots\;\tau_n$},
\end{displaymath}
where $T=\emph{dictTypeId}(C)$ and $C'=\emph{dictConstrId}(C)$, is
added to the source code and the type constructor and value type
environments are updated accordingly. Since type classes and type
constructors share a common name space, we simply use the identity
function for \emph{dictTypeId}.

Note that \texttt{bindDictConstr} transforms the types of the type
class methods and drops the first argument, which corresponds to the
type class constraint, in order to derive the types of the dictionary
constructor's arguments.
\begin{verbatim}

> bindDictTypes :: TCEnv -> TCEnv
> bindDictTypes = fmap transInfo
>   where transInfo (TypeClass cls _ _) = dictTypeInfo cls
>         transInfo ti = ti

> bindDictConstrs :: ModuleIdent -> TCEnv -> ValueEnv -> ValueEnv
> bindDictConstrs m tcEnv tyEnv =
>   foldr (bindDictConstr m tcEnv) tyEnv (allEntities tcEnv)

> bindDictConstr :: ModuleIdent -> TCEnv -> TypeInfo -> ValueEnv -> ValueEnv
> bindDictConstr m tcEnv (TypeClass cls _ fs) tyEnv =
>   bindEntity m c (DataConstructor c ty) tyEnv
>   where c = qualifyLike cls (dictConstrId (unqualify cls))
>         ty = polyType (classDictType tcEnv tyEnv cls fs)
> bindDictConstr _ _ _ tyEnv =  tyEnv

> dictDecl :: Position -> Ident -> Ident -> [MethodSig a] -> TopDecl Type
> dictDecl p cls tv ds =
>   DataDecl p [] (dictTypeId cls) [tv] [dictConstrDecl p cls tys]
>   where tys = [ty | MethodSig _ _ ty <- expandMethodSigs ds]
>         
> dictIDecl :: Position -> QualIdent -> Ident -> Maybe [Maybe IMethodDecl]
>           -> IDecl
> dictIDecl p cls tv (Just ds) =
>   IDataDecl p [] (qDictTypeId cls) [tv]
>             [Just (dictConstrDecl p (unqualify cls) tys)]
>   where tys = map (maybe (VariableType tv) methodType) ds
>         methodType (IMethodDecl _ _ ty) = ty
> dictIDecl p cls tv Nothing = HidingDataDecl p (qDictTypeId cls) [tv]

> expandMethodSigs :: [MethodSig a] -> [MethodSig a]
> expandMethodSigs ds = [MethodSig p [f] ty | MethodSig p fs ty <- ds, f <- fs]

> classDictType :: TCEnv -> ValueEnv -> QualIdent -> [Maybe Ident] -> Type
> classDictType tcEnv tyEnv cls fs =
>   foldr TypeArrow (dictType (TypePred cls (TypeVariable 0))) tys
>   where tys = map (maybe (TypeVariable 0) (classMethodType tyEnv cls n)) fs
>         n = 1 + length (superClasses cls tcEnv)

> classMethodType :: ValueEnv -> QualIdent -> Int -> Ident -> Type
> classMethodType tyEnv cls n f = arrows (transformType ty) !! n
>   where ForAll _ ty = funType (qualifyLike cls f) tyEnv
>         arrows ty = ty : case ty of {TypeArrow _ ty -> arrows ty; _ -> [] }

\end{verbatim}
\paragraph{Method Stubs}
For every type class method, a new global function is introduced.
These stub functions take a dictionary as first argument and return
the appropriate member function from the dictionary. For instance,
given the class declaration
\begin{verbatim}
  class Eq a where
    (==) :: a -> a -> Bool
    (/=) :: a -> a -> Bool
\end{verbatim}
two functions similar to
\begin{verbatim}
  (==) dict_Eq = case dict of { _Dict_Eq eq _ -> eq }
  (/=) dict_Eq = case dict of { _Dict_Eq _ neq -> neq }
\end{verbatim}
are introduced. When a class has super classes, additional arguments
are added for each of the direct and indirect super classes of the
class so that the stubs can be called like other overloaded functions.
For instance, given the class declarations
\begin{verbatim}
  class Eq a
  class Show a
  class (Eq a, Show a) => Num a where
    fromInteger :: Integer -> a
\end{verbatim}
a stub function similar to
\begin{verbatim}
  fromInteger dict_Eq dict_Num dict_Show =
    case dict_Num of { _Dict_Num fromInt -> fromInt }
\end{verbatim}
is defined. Note that the contexts of overloaded functions, and
therefore the dictionary arguments of the method stubs, are sorted
according to the qualified names of the type classes involved. This
necessitates the somewhat ugly construction of the stub methods'
contexts in \texttt{intfMethodStubs} below.
\begin{verbatim}

> methodStubs :: ModuleIdent -> TCEnv -> ValueEnv -> TopDecl a
>             -> DictState [TopDecl Type]
> methodStubs m tcEnv tyEnv (ClassDecl _ cx cls tv ds) =
>   do
>     us <- mapM (freshVar m "_#dict" . dictType) cx'
>     vs <- mapM (freshVar m "_#method") tys
>     return (zipWith (methodStub us (us!!n) (dictPattern ty cls' vs)) ds' vs)
>   where (tys,ty) = arrowUnapply (classDictType tcEnv tyEnv cls' (map Just fs))
>         cls' = qualifyWith m cls
>         cx' = context (expandPolyType tcEnv ty')
>         ty' = QualTypeExpr (ClassAssert cls' tv : cx) (VariableType tv)
>         n = fromJust (elemIndex (TypePred cls' (TypeVariable 0)) cx')
>         fs = concatMap methods ds
>         ds' = expandMethodSigs ds
>         context (ForAll _ (QualType cx _)) = cx
> methodStubs _ _ _ _ = return []

> methodStub :: [(Type,Ident)] -> (Type,Ident) -> ConstrTerm Type
>            -> MethodSig a -> (Type,Ident) -> TopDecl Type
> methodStub vs v t (MethodSig p [f] _) v' =
>   BlockDecl (funDecl p f (map (uncurry VariablePattern) vs) e [])
>   where e = Case (uncurry mkVar v) [caseAlt p t (uncurry mkVar v')]

> intfMethodStubs :: ModuleIdent -> IDecl -> [IDecl]
> intfMethodStubs m (IClassDecl _ cx cls tv ds) =
>   map (intfMethodStub cls (intfMethodContext m cx cls tv)) (catMaybes ds)
> intfMethodStubs _ _ = []

> intfMethodStub :: QualIdent -> [ClassAssert] -> IMethodDecl -> IDecl
> intfMethodStub cls cx (IMethodDecl p f ty) =
>   IFunctionDecl p (qualifyLike cls f) (QualTypeExpr cx ty)

> dictPattern :: Type -> QualIdent -> [(Type,Ident)] -> ConstrTerm Type
> dictPattern ty cls vs =
>   ConstructorPattern ty (qDictConstrId cls) (map (uncurry VariablePattern) vs)

> dictConstrDecl :: Position -> Ident -> [TypeExpr] -> ConstrDecl
> dictConstrDecl p cls tys = ConstrDecl p [] (dictConstrId cls) tys

> dictTypeInfo :: QualIdent -> TypeInfo
> dictTypeInfo cls =
>   DataType (qDictTypeId cls) 1 [Just (dictConstrId (unqualify cls))]

\end{verbatim}
\paragraph{Lifting default method implementations}
The default method implementations of a class must be available at
instance declarations so that they can be used instead of omitted
instance methods when creating instance dictionaries. To that end, the
compiler simply lifts default method declarations to the top-level.
Since the method names themselves are used for the method stubs, the
default implementations are renamed while they are lifted. In order to
avoid problems with hidden methods, whose names are not available in
the interface files, the lifted name is derived from the class' name
and the method's index. The lifted methods are then transformed just
like other overloaded functions (see \texttt{dictTransModule} above).

If the user does not provide a default implementation for a method,
the compiler provides a default implementation that is equivalent to
\texttt{Prelude.undefined}.

\ToDo{Use \texttt{Prelude.error} instead of \texttt{Prelude.undefined}
  as default implementation for omitted methods?}
\begin{verbatim}

> bindClassMethods :: ModuleIdent -> TCEnv -> ValueEnv -> ValueEnv
> bindClassMethods m tcEnv tyEnv =
>   foldr (bindDefaultMethods m) tyEnv (allEntities tcEnv)

> bindDefaultMethods :: ModuleIdent -> TypeInfo -> ValueEnv -> ValueEnv
> bindDefaultMethods m (TypeClass cls clss fs) tyEnv =
>   foldr ($) tyEnv
>         (zipWith (bindDefaultMethod m cls ty) fs (qDefaultMethodIds cls))
>   where ty = ForAll 1 (QualType cx tv)
>         cx = [TypePred cls tv | cls <- sort (cls : clss)]
>         tv = TypeVariable 0
> bindDefaultMethods _ _ tyEnv = tyEnv

> bindDefaultMethod :: ModuleIdent -> QualIdent -> TypeScheme -> Maybe Ident
>                   -> QualIdent -> ValueEnv -> ValueEnv
> bindDefaultMethod m cls ty f f' tyEnv =
>   bindEntity m f' (Value f' (maybe ty (methType tyEnv cls) f)) tyEnv
>   where methType tyEnv cls f = funType (qualifyLike cls f) tyEnv

> defaultMethodDecls :: ValueEnv -> TopDecl Type -> [TopDecl Type]
> defaultMethodDecls tyEnv (ClassDecl p _ cls _ ds) =
>   map BlockDecl (zipWith renameFunction (defaultMethodIds cls) vds'')
>   where (tds,vds) = partition isMethodSig ds
>         fs = concatMap methods tds
>         vds' = orderDefaultMethodDecls fs vds
>         vds'' = zipWith (defaultMethodDecl tyEnv p) fs vds'
> defaultMethodDecls _ _ = []

> defaultMethodDecl :: ValueEnv -> Position -> Ident -> Maybe (MethodSig Type)
>                   -> Decl Type
> defaultMethodDecl _ _ _ (Just d) = methodDecl d
>   where methodDecl (DefaultMethodDecl p f eqs) = FunctionDecl p f eqs
> defaultMethodDecl tyEnv p f Nothing =
>   funDecl p f [] (prelUndefined (rawType (varType f tyEnv))) []

> orderDefaultMethodDecls :: [Ident] -> [MethodSig a] -> [Maybe (MethodSig a)]
> orderDefaultMethodDecls fs ds =
>   map (flip lookup [(f,d) | d@(DefaultMethodDecl _ f _) <- ds]) fs

> intfDefaultMethodDecls :: ModuleIdent -> IDecl -> [IDecl]
> intfDefaultMethodDecls m (IClassDecl p cx cls tv ds) =
>   zipWith (intfDefaultMethodDecl p cx' ty) (qDefaultMethodIds cls) ds
>   where cx' = intfMethodContext m cx cls tv
>         ty = VariableType tv
> intfDefaultMethodDecls _ _ = []

> intfDefaultMethodDecl :: Position -> [ClassAssert] -> TypeExpr -> QualIdent
>                       -> Maybe IMethodDecl -> IDecl
> intfDefaultMethodDecl _ cx _ f (Just (IMethodDecl p _ ty)) =
>   IFunctionDecl p f (QualTypeExpr cx ty)
> intfDefaultMethodDecl p cx ty f Nothing =
>   IFunctionDecl p f (QualTypeExpr cx ty)

> intfMethodContext :: ModuleIdent -> [ClassAssert] -> QualIdent -> Ident
>                   -> [ClassAssert]
> intfMethodContext m cx cls tv =
>   [ClassAssert (qualUnqualify m cls) tv | cls <- sort clss]
>   where clss = map (qualQualify m) (cls : [cls | ClassAssert cls _ <- cx])

> defaultMethodIds :: Ident -> [Ident]
> defaultMethodIds cls = map (defaultMethodId cls) [1..]
>   where defaultMethodId cls n =
>           mkIdent ("_Method#" ++ name cls ++ "#" ++ show n)

> qDefaultMethodIds :: QualIdent -> [QualIdent]
> qDefaultMethodIds cls =
>   map (qualifyLike cls) (defaultMethodIds (unqualify cls))

\end{verbatim}
\paragraph{Instance Dictionaries}
For every instance declaration
\begin{displaymath}
  \mbox{\texttt{instance} \texttt{(}$C_1\,x_{i_1}$\texttt{,}
    \dots\texttt{,} $C_l\,x_{i_o}$\texttt{)} \texttt{=>}
    $C$ \texttt{($T\,x_1\dots\,x_l$)} \texttt{where} \texttt{\lb}
    $f_{i_1}$ \texttt{=} $e_{i_1}$\texttt{;} \dots\texttt{;}
    $f_{i_m}$ \texttt{=} $e_{i_m}$ \texttt{\rb}},
\end{displaymath}
where the instance methods $f_{i_1}, \dots, f_{i_m}$ are
a subset of the methods $f_1, \dots, f_n$ declared for class $C$, a
global function
\begin{displaymath}
  \mbox{$f$ $d_1$ $\dots\;d_o$ \texttt{=} $C'$ $g_1$ $\dots\;g_n$
    \texttt{where} \texttt{\lb} $h_{i_1}$ \texttt{=} $e_{i_1}$\texttt{;} 
    \dots\texttt{;} $h_{i_m}$ \texttt{=} $e_{i_m}$ \texttt{\rb}},
\end{displaymath}
where $f=\emph{instFunId}(C,T)$ and $C'=\emph{dictConstrId}(C)$ is
added to the source code and its type is recorded in the type
environment. The function receives a dictionary argument for each of
the type predicates $C_i\,x_i$ appearing in the instance context
similar to the transformation of overloaded functions (see below).
These dictionaries are in scope in the (transformed) method
implementations. We do not add explicit dictionary arguments to the
methods themselves because each of them might use only some of the
dictionaries.

The dictionary constructor's argument expressions $g_i$ are given by
\begin{displaymath}
  g_i =
    \left\{
      \begin{array}{ll}
        h_i & \mbox{if $i \in \left\{ i_1, \dots, i_m \right\}$,} \\
        f_i' & \mbox{otherwise,}
      \end{array}
    \right.
\end{displaymath}
where $f_i'$ is the name of the default method implementation of
method $f_i$ in class $C$. The instance methods are renamed using
fresh identifiers $h_{i_1}, \dots, h_{i_m}$ so that the local function
definitions do not shadow the class methods, which may be used --
possibly at a different type -- in the method implementations.
\begin{verbatim}

> bindInstFuns :: TCEnv -> InstEnv -> ValueEnv -> ValueEnv
> bindInstFuns tcEnv iEnv tyEnv =
>   foldr (bindInstFun tcEnv) tyEnv (envToList iEnv)

> bindInstFun :: TCEnv -> (CT,Context) -> ValueEnv -> ValueEnv
> bindInstFun tcEnv (ct,cx) =
>   importTopEnv False m f (Value (qualifyWith m f) (polyType ty))
>   where m = instanceMIdent
>         f = instFunId tp
>         ty = transDictType cx tp
>         tp = ctTypePred tcEnv ct

> ctTypePred :: TCEnv -> CT -> TypePred
> ctTypePred tcEnv (CT cls tc) = TypePred cls ty
>   where ty
>           | tc == qArrowId = TypeArrow (tvs !! 0) (tvs !! 1)
>           | otherwise = TypeConstructor tc (take (constrKind tc tcEnv) tvs)
>         tvs = map TypeVariable [0..]

> instDecl :: ModuleIdent -> TCEnv -> InstEnv -> ValueEnv -> Position
>          -> [ClassAssert] -> QualIdent -> TypeExpr -> [MethodDecl Type]
>          -> DictState (TopDecl Type)
> instDecl m tcEnv iEnv tyEnv p cx cls ty ds =
>   do
>     vs <- mapM (freshVar m "_#method") (arrowArgs ty')
>     liftM BlockDecl $
>       dictTrans m iEnv (foldr (bindMeth m) tyEnv' vs) emptyEnv $
>       funDecl p f [] (dictExpr ty' cls vs ds')
>               (catMaybes (zipWith (fmap . (renameMethod . snd)) vs ds'))
>   where f = instFunId tp
>         (cx',tp) = toTypePred (expandPolyType tcEnv) cx cls ty
>         fs = classMethods cls tcEnv
>         ds' = orderMethodDecls fs ds
>         ty' = instDictType tcEnv tyEnv tp fs ds'
>         tyEnv' = bindFun m f (typeScheme (qualDictType cx' tp)) tyEnv
>         renameMethod f = renameFunction f . methodDecl
>         bindMeth m (ty,v) = bindFun m v (monoType ty)
>         bindFun m f ty = localBindTopEnv f (Value (qualifyWith m f) ty)
>         methodDecl (MethodDecl p f eqs) = (FunctionDecl p f eqs)

> instIDecl :: ModuleIdent -> Position -> [ClassAssert] -> QualIdent -> TypeExpr
>           -> IDecl
> instIDecl m p cx cls ty =
>   IFunctionDecl p (qInstFunId tp) (fromTransType m (transDictType cx' tp))
>   where (cx',tp) = toTypePred (toTypeScheme m) cx (qualQualify m cls) ty

> toTypePred :: (QualTypeExpr -> TypeScheme) -> [ClassAssert]
>            -> QualIdent -> TypeExpr -> (Context,TypePred)
> toTypePred f cx cls ty = (cx',TypePred cls ty')
>   where ForAll _ (QualType cx' ty') = f (QualTypeExpr cx ty)

> orderMethodDecls :: [Maybe Ident] -> [MethodDecl a] -> [Maybe (MethodDecl a)]
> orderMethodDecls fs ds =
>   map (>>= flip lookup [(f,d) | d@(MethodDecl _ f _) <- ds]) fs

> instDictType :: TCEnv -> ValueEnv -> TypePred -> [Maybe Ident]
>              -> [Maybe (MethodDecl Type)] -> Type
> instDictType tcEnv tyEnv (TypePred cls ty) fs ds =
>   subst (matchInstMethodTypes (arrowArgs ty') ds idSubst) ty'
>   where ty' = expandAliasType [ty] (classDictType tcEnv tyEnv cls fs)

> dictExpr :: Type -> QualIdent -> [(Type,Ident)] -> [Maybe (MethodDecl a)]
>          -> Expression Type
> dictExpr ty cls vs ds =
>   apply (Constructor ty (qDictConstrId cls))
>         (zipWith3 instFun vs (qDefaultMethodIds cls) ds)
>   where instFun (ty,v) _ (Just _) = mkVar ty v
>         instFun (ty,_) f Nothing = Variable ty f

> renameFunction :: Ident -> Decl Type -> Decl Type
> renameFunction f (FunctionDecl p _ eqs) =
>   FunctionDecl p f (map (renameEqnLhs f) eqs)
>   where renameEqnLhs f (Equation p lhs rhs) = Equation p (renameLhs f lhs) rhs
>         renameLhs f (FunLhs _ ts) = FunLhs f ts
>         renameLhs f (OpLhs t1 _ t2) = OpLhs t1 f t2
>         renameLhs f (ApLhs lhs ts) = ApLhs (renameLhs f lhs) ts

\end{verbatim}
\paragraph{Adding Dictionary Arguments}
Given a function $f$ with type $(C_1\,x_1, \dots, C_n\,x_n)
\Rightarrow \tau$, the compiler adds $n$ implicit dictionary arguments
to the function's declaration thereby changing $f$'s type into
$T_1\,x_1 \rightarrow \dots \rightarrow T_n\,x_n \rightarrow \tau$,
where $T_i=\emph{dictTypeId}(C_i)$. The types of these variables are
recorded in the type environment and an environment mapping the
constraints $C_i\,x_i$ onto their corresponding dictionary arguments
is computed as well. This environment is used when transforming
function applications in $f$'s body.
\begin{verbatim}

> type DictEnv = Env TypePred (Expression Type)

> rebindFuns :: ValueEnv -> ValueEnv
> rebindFuns = fmap transInfo
>   where transInfo (Value f (ForAll n ty)) =
>           Value f (ForAll n (QualType [] (transformType ty)))
>         transInfo vi = vi

> class DictTrans a where
>   dictTrans :: ModuleIdent -> InstEnv -> ValueEnv -> DictEnv -> a Type
>             -> DictState (a Type)

> instance DictTrans Goal where
>   dictTrans m iEnv tyEnv dictEnv (Goal p e ds) =
>     liftM2 (Goal p)
>            (dictTrans m iEnv tyEnv dictEnv e)
>            (mapM (dictTrans m iEnv tyEnv dictEnv) ds)

> instance DictTrans Decl where
>   dictTrans m iEnv tyEnv dictEnv (FunctionDecl p f eqs) =
>     liftM (FunctionDecl p f) (mapM (dictTrans m iEnv tyEnv dictEnv) eqs)
>   dictTrans m iEnv tyEnv dictEnv (PatternDecl p t rhs) =
>     liftM (PatternDecl p t) (dictTrans m iEnv tyEnv dictEnv rhs)
>   dictTrans _ _ _ _ d = return d

> instance DictTrans Equation where
>   dictTrans m iEnv tyEnv dictEnv (Equation p lhs rhs) =
>     do
>       -- FIXME: could share dictionary variables between all equations
>       --        of a function => perform transformation in Decl instance
>       xs <- mapM (freshVar m "_#dict" . dictType) cx
>       liftM (Equation p (addArgs (map (uncurry VariablePattern) xs) lhs))
>             (dictTrans m iEnv tyEnv (foldr bindDict dictEnv (zip cx xs)) rhs)
>     where (f,ts) = flatLhs lhs
>           ty = foldr TypeArrow (typeOf rhs) (map typeOf ts)
>           cx = matchContext (varType f tyEnv) ty
>           bindDict (tp,x) = bindEnv tp (uncurry mkVar x)

> addArgs :: [ConstrTerm a] -> Lhs a -> Lhs a
> addArgs xs (FunLhs f ts) = FunLhs f (xs ++ ts)
> addArgs xs (OpLhs t1 op t2) = FunLhs op (xs ++ [t1,t2])
> addArgs xs (ApLhs lhs ts) = ApLhs (addArgs xs lhs) ts

> instance DictTrans Rhs where
>   dictTrans m iEnv tyEnv dictEnv (SimpleRhs p e ds) =
>     liftM2 (SimpleRhs p)
>            (dictTrans m iEnv tyEnv dictEnv e)
>            (mapM (dictTrans m iEnv tyEnv dictEnv) ds)
>   dictTrans m iEnv tyEnv dictEnv (GuardedRhs es ds) =
>     liftM2 GuardedRhs
>            (mapM (dictTrans m iEnv tyEnv dictEnv) es)
>            (mapM (dictTrans m iEnv tyEnv dictEnv) ds)

> instance DictTrans CondExpr where
>   dictTrans m iEnv tyEnv dictEnv (CondExpr p g e) =
>     liftM2 (CondExpr p)
>            (dictTrans m iEnv tyEnv dictEnv g)
>            (dictTrans m iEnv tyEnv dictEnv e)

\end{verbatim}
An application of an overloaded function $f$ with type $(C_1\,x_1,
\dots, C_n\,x_n) \Rightarrow \tau$ is changed into an application of
$f$ to the dictionaries for $C_1\,\tau_1, \dots, C_n\,\tau_n$ where
the types $\tau_i$ are given by $\tau_i = \vartheta x_i$ where
$\vartheta$ is the most general unifier between $f$'s type $\tau$ and
the concrete type at which $f$ is used in the application.
\begin{verbatim}

> transLiteral :: ModuleIdent -> InstEnv -> ValueEnv -> DictEnv -> Type
>              -> Literal -> DictState (Expression Type)
> transLiteral _ _ _ _ ty (Char c) = return (Literal ty (Char c))
> transLiteral m iEnv tyEnv dictEnv ty (Int i)
>   | ty == intType = return (Literal ty (Int i))
>   | ty == floatType = return (Literal ty (Float (fromIntegral i)))
>   | otherwise = dictTrans m iEnv tyEnv dictEnv
>                           (apply (prelFromInt ty) [Literal intType (Int i)])
> transLiteral m iEnv tyEnv dictEnv ty (Float f)
>   | ty == floatType = return (Literal ty (Float f))
>   | otherwise =
>       dictTrans m iEnv tyEnv dictEnv
>                 (apply (prelFromFloat ty) [Literal floatType (Float f)])
> transLiteral _ _ _ _ ty (String cs) = return (Literal ty (String cs))

> instance DictTrans Expression where
>   dictTrans m iEnv tyEnv dictEnv (Literal ty l) =
>     transLiteral m iEnv tyEnv dictEnv ty l
>   dictTrans _ iEnv tyEnv dictEnv (Variable ty v) =
>     return (apply (Variable ty' v) xs)
>     where ty' = foldr (TypeArrow . typeOf) ty xs
>           xs = map (dictArg iEnv dictEnv) (matchContext (funType v tyEnv) ty)
>   dictTrans _ _ _ _ (Constructor ty c) = return (Constructor ty c)
>   dictTrans m iEnv tyEnv dictEnv (Paren e) =
>     liftM Paren (dictTrans m iEnv tyEnv dictEnv e)
>   dictTrans m iEnv tyEnv dictEnv (Typed e ty) =
>     liftM (flip Typed ty) (dictTrans m iEnv tyEnv dictEnv e)
>   dictTrans m iEnv tyEnv dictEnv (Tuple es) =
>     liftM Tuple (mapM (dictTrans m iEnv tyEnv dictEnv) es)
>   dictTrans m iEnv tyEnv dictEnv (List ty es) =
>     liftM (List ty) (mapM (dictTrans m iEnv tyEnv dictEnv) es)
>   dictTrans m iEnv tyEnv dictEnv (ListCompr e sts) =
>     liftM2 ListCompr
>            (dictTrans m iEnv tyEnv dictEnv e)
>            (mapM (dictTrans m iEnv tyEnv dictEnv) sts)
>   dictTrans m iEnv tyEnv dictEnv (EnumFrom e) =
>     dictTrans m iEnv tyEnv dictEnv (apply (prelEnumFrom (typeOf e)) [e])
>   dictTrans m iEnv tyEnv dictEnv (EnumFromThen e1 e2) =
>     dictTrans m iEnv tyEnv dictEnv
>               (apply (prelEnumFromThen (typeOf e1)) [e1,e2])
>   dictTrans m iEnv tyEnv dictEnv (EnumFromTo e1 e2) =
>     dictTrans m iEnv tyEnv dictEnv
>               (apply (prelEnumFromTo (typeOf e1)) [e1,e2])
>   dictTrans m iEnv tyEnv dictEnv (EnumFromThenTo e1 e2 e3) =
>     dictTrans m iEnv tyEnv dictEnv
>               (apply (prelEnumFromThenTo (typeOf e1)) [e1,e2,e3])
>   dictTrans m iEnv tyEnv dictEnv (UnaryMinus e) =
>     dictTrans m iEnv tyEnv dictEnv (apply (prelNegate (typeOf e)) [e])
>   dictTrans m iEnv tyEnv dictEnv (Apply e1 e2) =
>     liftM2 Apply
>            (dictTrans m iEnv tyEnv dictEnv e1)
>            (dictTrans m iEnv tyEnv dictEnv e2)
>   dictTrans m iEnv tyEnv dictEnv (InfixApply e1 op e2) =
>     dictTrans m iEnv tyEnv dictEnv (apply (infixOp op) [e1,e2])
>   dictTrans m iEnv tyEnv dictEnv (LeftSection e op) =
>     dictTrans m iEnv tyEnv dictEnv (apply (infixOp op) [e])
>   dictTrans m iEnv tyEnv dictEnv (RightSection op e) =
>     dictTrans m iEnv tyEnv dictEnv (apply (prelFlip ty1 ty2 ty3) [op',e])
>     where TypeArrow ty1 (TypeArrow ty2 ty3) = typeOf op'
>           op' = infixOp op
>   dictTrans m iEnv tyEnv dictEnv (Lambda ts e) =
>     liftM (Lambda ts) (dictTrans m iEnv tyEnv dictEnv e)
>   dictTrans m iEnv tyEnv dictEnv (Let ds e) =
>     liftM2 Let
>            (mapM (dictTrans m iEnv tyEnv dictEnv) ds)
>            (dictTrans m iEnv tyEnv dictEnv e)
>   dictTrans m iEnv tyEnv dictEnv (Do sts e) =
>     liftM2 Do
>            (mapM (dictTrans m iEnv tyEnv dictEnv) sts)
>            (dictTrans m iEnv tyEnv dictEnv e)
>   dictTrans m iEnv tyEnv dictEnv (IfThenElse e1 e2 e3) =
>     liftM3 IfThenElse
>            (dictTrans m iEnv tyEnv dictEnv e1)
>            (dictTrans m iEnv tyEnv dictEnv e2)
>            (dictTrans m iEnv tyEnv dictEnv e3)
>   dictTrans m iEnv tyEnv dictEnv (Case e as) =
>     liftM2 Case
>            (dictTrans m iEnv tyEnv dictEnv e)
>            (mapM (dictTrans m iEnv tyEnv dictEnv) as)

> instance DictTrans Alt where
>   dictTrans m iEnv tyEnv dictEnv (Alt p t rhs) =
>     liftM (Alt p t) (dictTrans m iEnv tyEnv dictEnv rhs)

> instance DictTrans Statement where
>   dictTrans m iEnv tyEnv dictEnv (StmtExpr e) =
>     liftM StmtExpr (dictTrans m iEnv tyEnv dictEnv e)
>   dictTrans m iEnv tyEnv dictEnv (StmtBind t e) =
>     liftM (StmtBind t) (dictTrans m iEnv tyEnv dictEnv e)
>   dictTrans m iEnv tyEnv dictEnv (StmtDecl ds) =
>     liftM StmtDecl (mapM (dictTrans m iEnv tyEnv dictEnv) ds)

> transformType :: QualType -> Type
> transformType (QualType cx ty) = foldr (TypeArrow . dictType) ty cx

\end{verbatim}
The function \texttt{dictArg} is the heart of the dictionary
transformation algorithm for expressions. It constructs the dictionary
argument for a type predicate from the context of a type class method
or overloaded function. To that end, it checks whether a dictionary
for the type predicate is available in the dictionary environment,
which is the case when the predicate's type is a type variable, and
uses \texttt{instDict} otherwise in order to supply a new dictionary
using the appropriate instance dictionary construction function. If
the corresponding instance declaration has a non-empty context, the
dictionary construction function is applied to the dictionaries
computed for the context instantiated at the appropriate types.

\ToDo{The transformed code should share instance dictionaries whenever
  possible. For instance, just one \texttt{Num} \texttt{Float}
  dictionary should be created for the expression
  \texttt{x*x + y*y :: Float}.}
\begin{verbatim}

> dictArg :: InstEnv -> DictEnv -> TypePred -> Expression Type
> dictArg iEnv dictEnv tp =
>   fromMaybe (instDict iEnv dictEnv tp) (lookupEnv tp dictEnv)

> instDict :: InstEnv -> DictEnv -> TypePred -> Expression Type
> instDict iEnv dictEnv (TypePred cls ty) =
>   case lookupEnv (CT cls tc) iEnv of
>     Just cx ->
>       instFunApp iEnv dictEnv (map (expandAliasType tys) cx) (TypePred cls ty)
>     Nothing -> internalError ("instDict " ++ show cls ++ " " ++ show tc)
>   where (tc,tys) = unapplyType ty
>         unapplyType (TypeConstructor tc tys) = (tc,tys)
>         unapplyType (TypeVariable _) = internalError "unapplyType"
>         unapplyType (TypeConstrained tys _) = unapplyType (head tys)
>         unapplyType (TypeArrow ty1 ty2) = (qArrowId,[ty1,ty2])
>         unapplyType (TypeSkolem _) = internalError "unapplyType"

> instFunApp :: InstEnv -> DictEnv -> Context -> TypePred -> Expression Type
> instFunApp iEnv dictEnv cx tp =
>   apply (Variable (transDictType cx tp) (qInstFunId tp))
>         (map (dictArg iEnv dictEnv) cx)

\end{verbatim}
\paragraph{Unification}
When adding dictionary arguments on the left hand side of an equation
and in applications, respectively, the compiler must unify the
function's type with the concrete instance at which that type is used
in order to determine the correct context. This problem does not
require a general unification because only the polymorphic type
variables of the function's type can be instantiated to a particular
monomorphic type. Furthermore, as long as no newtype constructors have
been removed all occurrences of a particular type variable must be
instantiated to exactly the same type.\footnote{If newtype
  constructors are removed, different occurrences may be instantiated
  to different but equivalent types. E.g., given a declaration
  \texttt{newtype CInt = CInt Int}, a type variable can be
  instantiated to \texttt{Int} at one place and to \texttt{CInt} at
  another place.}
\begin{verbatim}

> matchContext :: TypeScheme -> Type -> Context
> matchContext (ForAll _ (QualType cx ty1)) ty2 =
>   subst (match ty1 ty2 idSubst) cx

> match :: Type -> Type -> TypeSubst -> TypeSubst
> match (TypeConstructor tc1 tys1) (TypeConstructor tc2 tys2)
>   | tc1 == tc2 = matchTypes tys1 tys2
> match (TypeVariable tv) ty
>   | tv >= 0 = bindSubst tv ty
> match (TypeVariable tv1) (TypeVariable tv2)
>   | tv1 == tv2 = id
> match (TypeConstrained _ tv1) (TypeConstrained _ tv2)
>   | tv1 == tv2 = id
> match (TypeArrow ty11 ty12) (TypeArrow ty21 ty22) =
>   matchTypes [ty11,ty12] [ty21,ty22]
> match (TypeSkolem k1) (TypeSkolem k2)
>   | k1 == k2 = id
> match ty1 ty2 =
>   internalError ("match (" ++ show ty1 ++ ") (" ++ show ty2 ++ ")")

> matchTypes :: [Type] -> [Type] -> TypeSubst -> TypeSubst
> matchTypes [] [] = id
> matchTypes (ty1:tys1) (ty2:tys2) = match ty1 ty2 . matchTypes tys1 tys2

> matchInstMethodTypes :: [Type] -> [Maybe (MethodDecl Type)] -> TypeSubst
>                      -> TypeSubst
> matchInstMethodTypes [] [] = id
> matchInstMethodTypes (ty:tys) (d:ds) =
>   maybe id (match ty . methodType) d . matchInstMethodTypes tys ds
>   where methodType (MethodDecl _ _ (Equation _ lhs rhs : _)) =
>           foldr (TypeArrow . typeOf) (typeOf rhs) (snd (flatLhs lhs))

\end{verbatim}
\paragraph{Auxiliary Functions}
The functions \texttt{dictTypeId} and \texttt{dictConstrId} return the
names of the dictionary type and data constructors for a class,
respectively. The function \texttt{qDictTypeId} and
\texttt{qDictConstrId} are variants of these functions that use
qualified names. Since type classes and type constructors share a
common name space, we simply reuse the type class name for its
dictionary type.
\begin{verbatim}

> dictTypeId :: Ident -> Ident
> dictTypeId = id

> qDictTypeId :: QualIdent -> QualIdent
> qDictTypeId cls = qualifyLike cls (dictTypeId (unqualify cls))

> dictConstrId :: Ident -> Ident
> dictConstrId cls = mkIdent ("_Dict#" ++ name cls)

> qDictConstrId :: QualIdent -> QualIdent
> qDictConstrId cls = qualifyLike cls (dictConstrId (unqualify cls))

\end{verbatim}
The functions \texttt{instFunId} and \texttt{qInstFunId} return the
name of the global function which returns the dictionary for a
particular C-T instance pair. Note that all instances are assumed to
be defined in a pseudo module whose module name is empty.  This
reflects the fact that instances are global and not tied to the
particular module that implements them.
\begin{verbatim}

> instanceMIdent :: ModuleIdent
> instanceMIdent = emptyMIdent

> instFunId :: TypePred -> Ident
> instFunId (TypePred cls ty) =
>   mkIdent ("_Inst#" ++ qualName cls ++ "#" ++ typeName ty)
>   where typeName (TypeConstructor tc _) = qualName tc
>         typeName (TypeConstrained tys _) = typeName (head tys)
>         typeName (TypeArrow _ _) = name arrowId
>         typeName ty = internalError ("instFunId " ++ show ty)

> qInstFunId :: TypePred -> QualIdent
> qInstFunId = qualifyWith instanceMIdent . instFunId

\end{verbatim}
The functions \texttt{dictType} and \texttt{qualDictType} return the
(qualified) type of the dictionary corresponding to a particular
$C$-$T$ instance.
\begin{verbatim}

> dictType :: TypePred -> Type
> dictType (TypePred cls ty) = TypeConstructor (qDictTypeId cls) [ty]

> qualDictType :: Context -> TypePred -> QualType
> qualDictType cx tp = QualType cx (dictType tp)

> transDictType :: Context -> TypePred -> Type
> transDictType cx tp = transformType (qualDictType cx tp)

\end{verbatim}
The function \texttt{bindEntity} introduces a binding for an entity
into a top-level environment. Depending on whether the entity is
defined in the current module or not, either an unqualified and a
qualified local binding or a qualified import are added to the
environment.
\begin{verbatim}

> bindEntity :: Entity a => ModuleIdent -> QualIdent -> a -> TopEnv a
>            -> TopEnv a
> bindEntity m x =
>   uncurry (maybe (globalBindTopEnv m) qualImportTopEnv)
>           (splitQualIdent (qualUnqualify m x))

\end{verbatim}
The monad transformer \texttt{freshVar} returns a new identifier and
records it in the type environment.
\begin{verbatim}

> freshVar :: ModuleIdent -> String -> Type -> DictState (Type,Ident)
> freshVar m pre ty =
>   do
>     x <- liftM (mkIdent . (pre ++) . show) (liftSt (updateSt (1 +)))
>     updateSt_ (localBindTopEnv x (Value (qualifyWith m x) (monoType ty)))
>     return (ty,x)

\end{verbatim}
Convenience functions for constructing parts of the syntax tree.
\begin{verbatim}

> funDecl :: Position -> Ident -> [ConstrTerm a] -> Expression a -> [Decl a]
>         -> Decl a
> funDecl p f ts e ds =
>   FunctionDecl p f [Equation p (FunLhs f ts) (SimpleRhs p e ds)]

> caseAlt :: Position -> ConstrTerm a -> Expression a -> Alt a
> caseAlt p t e = Alt p t (SimpleRhs p e [])

> mkVar :: a -> Ident -> Expression a
> mkVar a = Variable a . qualify

> apply :: Expression a -> [Expression a] -> Expression a
> apply = foldl Apply

\end{verbatim}
Prelude entities.

\ToDo{Desugar infix applications and sections before applying the
  dictionary transformation.}
\begin{verbatim}

> prelFlip :: Type -> Type -> Type -> Expression Type
> prelFlip a b c =
>   Variable (opType a b c `TypeArrow` opType b a c)
>            (qualifyWith preludeMIdent (mkIdent "flip"))
>   where opType a b c = a `TypeArrow` (b `TypeArrow` c)

> prelEnumFrom :: Type -> Expression Type
> prelEnumFrom a =
>   Variable (a `TypeArrow` listType a)
>            (qualifyWith preludeMIdent (mkIdent "enumFrom"))

> prelEnumFromThen :: Type -> Expression Type
> prelEnumFromThen a =
>   Variable (a `TypeArrow` (a `TypeArrow` listType a))
>            (qualifyWith preludeMIdent (mkIdent "enumFromThen"))

> prelEnumFromTo :: Type -> Expression Type
> prelEnumFromTo a =
>   Variable (a `TypeArrow` (a `TypeArrow` listType a))
>            (qualifyWith preludeMIdent (mkIdent "enumFromTo"))

> prelEnumFromThenTo :: Type -> Expression Type
> prelEnumFromThenTo a =
>   Variable (a `TypeArrow` (a `TypeArrow` (a `TypeArrow` listType a)))
>            (qualifyWith preludeMIdent (mkIdent "enumFromThenTo"))

> prelNegate :: Type -> Expression Type
> prelNegate a =
>   Variable (a `TypeArrow` a) (qualifyWith preludeMIdent (mkIdent "negate"))

> prelFromInt :: Type -> Expression Type
> prelFromInt a =
>   Variable (intType `TypeArrow` a)
>            (qualifyWith preludeMIdent (mkIdent "fromInt"))

> prelFromFloat :: Type -> Expression Type
> prelFromFloat a =
>   Variable (floatType `TypeArrow` a)
>            (qualifyWith preludeMIdent (mkIdent "fromFloat"))

> prelUndefined :: Type -> Expression Type
> prelUndefined a = Variable a (qualifyWith preludeMIdent (mkIdent "undefined"))

\end{verbatim}
