% -*- LaTeX -*-
% $Id: DictTrans.lhs 3056 2011-10-07 16:27:03Z wlux $
%
% Copyright (c) 2006-2011, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{DictTrans.lhs}
\section{Introducing Dictionaries}\label{sec:dict-trans}
For the implementation of type classes, we follow the common approach
to use dictionaries~\cite{PetersonJones93:TypeClasses}. For every type
predicate in the (reduced) context of a function's type we introduce
an implicit dictionary argument. The dictionaries themselves are
derived from the type class and instance declarations in the module.
\begin{verbatim}

> module DictTrans(dictTransModule, dictSpecializeModule) where
> import Base
> import Combined
> import Curry
> import CurryUtils
> import Env
> import InstInfo
> import Kinds
> import List
> import Maybe
> import Monad
> import PredefIdent
> import TopEnv
> import TrustInfo
> import Types
> import TypeInfo
> import TypeSubst
> import TypeTrans
> import Typing
> import Utils
> import ValueInfo

\end{verbatim}
The introduction of dictionaries proceeds in three phases. In the
first phase, the compiler adds data type declarations for the
dictionary constructors to the source code, introduces new top-level
functions for creating instance dictionaries, and lifts class and
instance method implementations to the top-level. The identifiers for
the dictionary data types and the lifted class and instance methods
are added to the module's export list, since the compiler may use them
directly from other modules.

Lifting default class method implementations is necessary so that the
compiler can use them in place of omitted instance methods. Lifting
instance method declarations allows calling methods directly when a
method is applied at a known type, which can improve performance
considerably. While lifting method implementations we also update the
arities recorded for the default methods in the type class environment
and for instance methods in the instance environment.

In the second phase, the compiler introduces dictionary arguments in
the left hand sides of overloaded function declarations and lifted
method declarations, and transforms occurrences of overloaded
functions and methods in expressions into applications to the
appropriate dictionary arguments.

In addition, the compiler introduces a method stub function for each
type class method that extracts the corresponding method
implementation from the type class's dictionary, and a function for
each super class of a type class that extract the super class's
dictionary from that of its subclass.

In the final phase, the compiler optimizes method calls at known types
by calling the appropriate instance methods directly. For instance,
the application \verb|show 'a'| has been translated into
\texttt{show \textit{dict\char`_Show\char`_Char} 'a'} during the
second phase of the dictionary transformation and is now optimized
into \texttt{\textit{show\char`_Char} 'a'}, where
\texttt{\textit{dict\char`_Show\char`_Char}} denotes an expression
that returns the dictionary of the \texttt{Show} \texttt{Char}
instance and \texttt{\textit{show\char`_Char}} the \texttt{show}
implementation of that instance.

The first two phases are implemented in function
\texttt{dictTransModule} and the specialization phase is
implemented in \texttt{dictSpecializeModule} on
p.~\pageref{dict-specialize}.

In order to generate unique names for the implicit dictionary
arguments introduced in the second phase we use a state monad.

\textbf{Note:} The \texttt{InstanceDecl} equation of function
\texttt{liftDecls} deliberately uses \texttt{toQualType} instead of
\texttt{expandPolyType} when converting the instance type. Since
renaming types have been changed into type synonyms, the compiler
would otherwise expand the instance type. Fortunately, no real type
synonyms can occur in the instance type, since instances can be
defined only for data and renaming types and all arguments must be
type variables (cf.\ Sect.~4.3.2 of~\cite{PeytonJones03:Haskell}).
\begin{verbatim}

> type DictState a = StateT Int Id a

> dictTransModule :: TCEnv -> InstEnv -> ValueEnv -> TrustEnv -> Module QualType
>                 -> (TCEnv,ValueEnv,TrustEnv,Module Type)
> dictTransModule tcEnv iEnv tyEnv trEnv (Module m es is ds) = flip runSt 1 $
>   do
>     ds' <- mapM (dictTrans tcEnv'' iEnv' tyEnv' [])
>                 (concatMap (liftDecls m tcEnv tyEnv) ds)
>     dss <- mapM (methodStubs m tcEnv tyEnv) ds
>     return (tcEnv'',tyEnv'',trEnv',Module m es' is (ds' ++ concat dss))
>   where es' = addExports es (concatMap (dictExports m tcEnv) ds)
>         tcEnv' = foldr (updateDefaultArities m) tcEnv ds
>         iEnv' = foldr updateInstArities iEnv ds
>         tyEnv' = bindClassDecls m tcEnv' (bindInstDecls m tcEnv iEnv' tyEnv)
>         tcEnv'' = bindDictTypes m tcEnv'
>         tyEnv'' = dictTransValues tyEnv'
>         trEnv' = foldr (liftTrustAnnots m) trEnv ds
>         addExports (Just (Exporting p es)) es' =
>           Just (Exporting p (es ++ es'))

> dictExports :: ModuleIdent -> TCEnv -> TopDecl a -> [Export]
> dictExports _ _ (DataDecl _ _ _ _ _ _) = []
> dictExports _ _ (NewtypeDecl _ _ _ _ _ _) = []
> dictExports _ _ (TypeDecl _ _ _ _) = []
> dictExports m tcEnv (ClassDecl _ _ cls _ _) = classExports m tcEnv cls
> dictExports m tcEnv (InstanceDecl _ _ cls ty _) =
>   instExports m tcEnv cls (toType [] ty)
> dictExports _ _ (DefaultDecl _ _) = []
> dictExports _ _ (BlockDecl _) = []

> liftDecls :: ModuleIdent -> TCEnv -> ValueEnv -> TopDecl QualType
>           -> [TopDecl QualType]
> liftDecls _ _ _ (DataDecl p cx tc tvs cs _) = [DataDecl p cx tc tvs cs []]
> liftDecls _ _ _ (NewtypeDecl p cx tc tvs nc _) =
>   [NewtypeDecl p cx tc tvs nc []]
> liftDecls _ _ _ (TypeDecl p tc tvs ty) = [TypeDecl p tc tvs ty]
> liftDecls m tcEnv tyEnv (ClassDecl p _ cls tv ds) =
>   classDecls tcEnv tyEnv p (qualifyWith m cls) tv ds
> liftDecls m tcEnv tyEnv (InstanceDecl p cx cls ty ds) =
>   -- NB Don't use expandPolyType tcEnv (QualTypeExpr cx ty) here!
>   instDecls m tcEnv tyEnv p cls (contextMap (sort . minContext tcEnv) ty') ds
>   where ty' = toQualType (QualTypeExpr cx ty)
> liftDecls _ _ _ (DefaultDecl _ _) = []
> liftDecls _ _ _ (BlockDecl d) = [BlockDecl d]

> updateDefaultArities :: ModuleIdent -> TopDecl a -> TCEnv -> TCEnv
> updateDefaultArities m (ClassDecl _ _ cls _ ds) tcEnv =
>   case qualLookupTopEnv (qualifyWith m cls) tcEnv of
>     [TypeClass cls' k clss fs] ->
>       globalRebindTopEnv m cls (TypeClass cls' k clss fs'') tcEnv
>       where fs'' = [(f,fromMaybe n (lookup f fs')) | (f,n) <- fs]
>     _ -> internalError ("updateDefaultArities" ++ show cls)
>   where fs' = methodArities ds
> updateDefaultArities _ _ tcEnv = tcEnv

> updateInstArities :: TopDecl a -> InstEnv -> InstEnv
> updateInstArities (InstanceDecl _ _ cls ty ds) iEnv =
>   case lookupEnv ct iEnv of
>     Just (m,cx,_) -> bindEnv ct (m,cx,methodArities ds) iEnv
>     Nothing -> internalError ("updateInstArities " ++ show ct)
>   where ct = CT cls (rootOfType (toType [] ty))
> updateInstArities _ iEnv = iEnv

> methodArities :: [Decl a] -> [(Ident,Int)]
> methodArities ds =
>   [(unRenameIdent f,eqnArity (head eqs)) | FunctionDecl _ _ f eqs <- ds]

\end{verbatim}
\paragraph{Class Declarations}
For every type class declaration
\begin{quote}
  \texttt{class} \texttt{(}$C_1$ $a$, \dots, $C_m$ $a$\texttt{)}
  \texttt{=>} $C$ $a$ \texttt{where} \texttt{\lb} $f_1$ \texttt{::}
  $\tau_1$\texttt{;} \dots\texttt{;} $f_n$ \texttt{::} $\tau_n$
  \texttt{\rb}
\end{quote}
a dictionary type declaration
\begin{quote}
  \texttt{data} $T$ $a$ \texttt{=} $C'$ \texttt{(}$T_1$
  $a$\texttt{)} \dots{} \texttt{(}$T_m$ $a$\texttt{)}  $\tau_1$
  $\dots\;\tau_n$,
\end{quote}
where $T=\emph{dictTypeId}(C)$, $T_i=\emph{dictTypeId}(C_i)$, and
$C'=\emph{dictConstrId}(C)$, is added to the source code and the type
constructor and value type environments are updated accordingly.

For polymorphic methods we have to cheat a little bit, since our type
representation does not support polymorphic components. We simply use
the method types recorded in the type environment when computing the
type of a dictionary constructor. This means that the methods'
polymorphic type variables -- i.e., all type variables other than the
class' type variable -- are assigned indices greater than 0
independently in each argument of the dictionary constructor. Explicit
dictionary arguments are added to the methods' types in place of the
constraints on their polymorphic type variables using
\texttt{transformMethodType}. Note that that function carefully drops
the first constraint, which corresponds to the type class constraint,
from the method's type before adding dictionary arguments.

The default method implementations of a class must be visible in
instance declarations so that they can be used instead of omitted
instance methods when creating instance dictionaries. To that end, the
compiler simply lifts default method declarations to the top-level.
The default method implementations are renamed during lifting in order
to avoid name conflicts with the method names themselves. If the user
does not provide a default implementation for a method, the compiler
uses a default implementation that is equivalent to
\texttt{Prelude.undefined}.

\ToDo{Use \texttt{Prelude.error} instead of \texttt{Prelude.undefined}
  as default implementation for omitted methods?}
\begin{verbatim}

> bindDictTypes :: ModuleIdent -> TCEnv -> TCEnv
> bindDictTypes m tcEnv = foldr (bindDictType m) tcEnv (allEntities tcEnv)

> bindDictType :: ModuleIdent -> TypeInfo -> TCEnv -> TCEnv
> bindDictType m (TypeClass cls k _ _) =
>   bindEntity m tc (DataType tc (KindArrow k KindStar) [c])
>   where tc = qDictTypeId cls
>         c = dictConstrId cls
> bindDictType _ _ = id

> bindClassDecls :: ModuleIdent -> TCEnv -> ValueEnv -> ValueEnv
> bindClassDecls m tcEnv tyEnv =
>   foldr (bindClassEntities m tcEnv) tyEnv (allEntities tcEnv)

> bindClassEntities :: ModuleIdent -> TCEnv -> TypeInfo -> ValueEnv -> ValueEnv
> bindClassEntities m tcEnv (TypeClass cls _ clss fs) tyEnv =
>   bindClassDict m (qDictConstrId cls) (classDictType tcEnv tyEnv cls fs) $
>   foldr (bindSuperClass m cls)
>         (foldr (bindDefaultMethod m tyEnv cls) tyEnv fs)
>         clss
> bindClassEntities _ _ _ tyEnv = tyEnv

> bindClassDict :: ModuleIdent -> QualIdent -> QualType -> ValueEnv -> ValueEnv
> bindClassDict m c (QualType cx ty) =
>   bindEntity m c (DataConstructor c ls ci (typeScheme (QualType cx ty)))
>   where ci = ConstrInfo 0 cx
>         ls = replicate (arrowArity ty) anonId

> bindDefaultMethod :: ModuleIdent -> ValueEnv -> QualIdent -> (Ident,Int)
>                   -> ValueEnv -> ValueEnv
> bindDefaultMethod m tyEnv cls (f,n) =
>   bindMethod m (qDefaultMethodId cls f) n (classMethodType tyEnv cls f)

> classExports :: ModuleIdent -> TCEnv -> Ident -> [Export]
> classExports m tcEnv cls =
>   ExportTypeWith (qDictTypeId cls') [dictConstrId cls'] :
>   map (Export . qSuperDictId cls') (superClasses cls' tcEnv) ++
>   map (Export . qDefaultMethodId cls' . fst) (classMethods cls' tcEnv)
>   where cls' = qualifyWith m cls

> classDecls :: TCEnv -> ValueEnv -> Position -> QualIdent -> Ident
>            -> [Decl QualType] -> [TopDecl QualType]
> classDecls tcEnv tyEnv p cls tv ds =
>   dictDataDecl tcEnv p cls tv ods :
>   map (uncurry (defaultMethodDecl tyEnv cls (methodMap vds))) fs
>   where (vds,ods) = partition isValueDecl ds
>         fs = [(p,f) | TypeSig p fs _ <- ods, f <- fs]

> dictDataDecl :: TCEnv -> Position -> QualIdent -> Ident -> [Decl a]
>              -> TopDecl a
> dictDataDecl tcEnv p cls tv ds =
>   DataDecl p [] (dictTypeId cls) [tv] [dictConstrDecl p cls tv clss tys] []
>   where clss = superClasses cls tcEnv
>         tys = map (expandMethodType tcEnv cls tv)
>                   [ty | TypeSig _ fs ty <- ds, _ <- fs]

> defaultMethodDecl :: ValueEnv -> QualIdent -> [(Ident,Decl QualType)]
>                   -> Position -> Ident -> TopDecl QualType
> defaultMethodDecl tyEnv cls ds p f =
>   methodDecl qUndefinedId p (defaultMethodId cls f) ty (lookup f ds)
>   where ForAll _ ty = varType f tyEnv

> classDictType :: TCEnv -> ValueEnv -> QualIdent -> MethodList -> QualType
> classDictType tcEnv tyEnv cls =
>   QualType [TypePred cls (TypeVariable 0) | cls <- superClasses cls tcEnv] .
>   foldr (TypeArrow . transformMethodType . classMethodType tyEnv cls . fst) ty
>   where ty = dictType (TypePred cls (TypeVariable 0))

> classMethodType :: ValueEnv -> QualIdent -> Ident -> QualType
> classMethodType tyEnv cls f = ty
>   where ForAll _ ty = funType (qualifyLike cls f) tyEnv

> dictConstrDecl :: Position -> QualIdent -> Ident -> [QualIdent] -> [QualType]
>                -> ConstrDecl
> dictConstrDecl p cls tv clss tys =
>   ConstrDecl p (filter (tv /=) (nub (fv tys'))) cx (dictConstrId cls) tys'
>   where tvs = tv : filter (unRenameIdent tv /=) nameSupply
>         cx = [ClassAssert cls (VariableType tv) | cls <- clss]
>         tys' = map (fromType tvs . transformMethodType) tys

> transformMethodType :: QualType -> Type
> transformMethodType = transformType . contextMap tail

\end{verbatim}
\paragraph{Super Class Dictionaries and Method Stubs}
For each super class and each method of a type class, a new global
function is introduced. These stub functions take a dictionary as
first argument and return the corresponding super class's dictionary
and the appropriate member function, respectively, from the
dictionary. For instance, given the class declaration
\begin{verbatim}
  class Eq a where
    (==) :: a -> a -> Bool
    (/=) :: a -> a -> Bool
\end{verbatim}
two functions similar to
\begin{verbatim}
  (==) dict_Eq = case dict_Eq of { _Dict_Eq eq _ -> eq }
  (/=) dict_Eq = case dict_Eq of { _Dict_Eq _ neq -> neq }
\end{verbatim}
are introduced.

Polymorphic methods with type class constraints add a little
complication. For instance, consider the class
\begin{verbatim}
  class T a where
    f :: Eq b => b -> a -> a
\end{verbatim}
Since \texttt{f} effectively has two dictionary arguments, the
compiler will expect its method stub to be a binary function. However,
the method stub must use only the first of these dictionaries in order
to determine the instance method and pass on the second dictionary
argument to the implementation method. Therefore, \texttt{f}'s method
stub must be similar to
\begin{verbatim}
  f dict_T dict_Eq =
    case dict_T of { _Dict_T f -> f dict_Eq }
\end{verbatim}
Obviously, each method stub must use its own list of dictionary
arguments for the class constraints appearing in its method
declaration. On the other hand, the dictionary arguments for the
method's class can be shared among all method stubs of that class.
\begin{verbatim}

> bindSuperClass :: ModuleIdent -> QualIdent -> QualIdent -> ValueEnv
>                -> ValueEnv
> bindSuperClass m cls super = bindEntity m f (Value f 1 (polyType ty))
>   where f = qSuperDictId cls super
>         ty = superDictType cls super (TypeVariable 0)

> superDictType :: QualIdent -> QualIdent -> Type -> Type
> superDictType cls super ty =
>   TypeArrow (dictType (TypePred cls ty)) (dictType (TypePred super ty))

> methodStubs :: ModuleIdent -> TCEnv -> ValueEnv -> TopDecl a
>             -> DictState [TopDecl Type]
> methodStubs m tcEnv tyEnv (ClassDecl p _ cls tv ds) =
>   do
>     u <- freshVar "_#dict" (instType (dictType tp))
>     uss <- mapM (mapM (freshVar "_#dict" . instType)) tyss
>     vsD <- mapM (freshVar "_#dict" . instType) tysD
>     vsM <- mapM (freshVar "_#meth" . instType) tysM
>     let t = dictPattern (instType ty') cls' (vsD ++ vsM)
>     return (zipWith3 (superDictDecl u t p cls') tysD' clss vsD ++
>             zipWith5 (methodStubDecl u t) ps tysM' fs vsM uss)
>   where cls' = qualifyWith m cls
>         tp = TypePred cls' (TypeVariable 0)
>         QualType cx ty = classDictType tcEnv tyEnv cls' [(f,0) | f <- fs]
>         (tys,ty') = arrowUnapply (transformType (QualType cx ty))
>         (tysD,tysM) = splitAt (length cx) tys
>         (tysD',tysM') =
>           splitAt (length cx) (map (TypeArrow (dictType tp)) tys)
>         clss = [cls | TypePred cls _ <- cx]
>         tyss = zipWith (methodDictTypes tyEnv) fs tysM
>         (ps,fs) = unzip [(p,f) | TypeSig p fs _ <- ds, f <- fs]
> methodStubs _ _ _ _ = return []

> superDictDecl :: (a,Ident) -> ConstrTerm a -> Position -> QualIdent
>               -> a -> QualIdent -> (a,Ident) -> TopDecl a
> superDictDecl u t p cls ty super v =
>   functDecl p ty (superDictId cls super) [uncurry VariablePattern u]
>             (methodStubExpr u t p v [])

> methodStubDecl :: (a,Ident) -> ConstrTerm a -> Position -> a -> Ident
>                -> (a,Ident) -> [(a,Ident)] -> TopDecl a
> methodStubDecl u t p ty f v us =
>   functDecl p ty f (map (uncurry VariablePattern) (u:us))
>             (methodStubExpr u t p v us)

> methodDictTypes :: ValueEnv -> Ident -> Type -> [Type]
> methodDictTypes tyEnv f ty =
>   take (length tys - arrowArity (rawType (varType f tyEnv))) tys
>   where tys = arrowArgs ty

> dictPattern :: a -> QualIdent -> [(a,Ident)] -> ConstrTerm a
> dictPattern ty cls vs =
>   ConstructorPattern ty (qDictConstrId cls) (map (uncurry VariablePattern) vs)

> methodStubExpr :: (a,Ident) -> ConstrTerm a -> Position -> (a,Ident)
>                -> [(a,Ident)] -> Expression a
> methodStubExpr u t p v us =
>   Case (uncurry mkVar u)
>        [caseAlt p t (apply (uncurry mkVar v) (map (uncurry mkVar) us))]

> instQualType :: QualType -> QualType
> instQualType (QualType cx ty) = QualType (map instTypePred cx) (instType ty)

> instTypePred :: TypePred -> TypePred
> instTypePred (TypePred cls ty) = TypePred cls (instType ty)

> instType :: Type -> Type
> instType (TypeConstructor tc) = TypeConstructor tc
> instType (TypeVariable tv) = TypeVariable (-1 - tv)
> instType (TypeApply ty1 ty2) = TypeApply (instType ty1) (instType ty2)
> instType (TypeArrow ty1 ty2) = TypeArrow (instType ty1) (instType ty2)

\end{verbatim}
\paragraph{Instance Declarations}
For every instance declaration
\begin{displaymath}
  \mbox{\texttt{instance} \texttt{(}$C_1\,u_{i_1}$\texttt{,}
    \dots\texttt{,} $C_l\,u_{i_l}$\texttt{)} \texttt{=>}
    $C$ \texttt{($T\,u_1\dots\,u_l$)} \texttt{where} \texttt{\lb}
    $h_{i_1}$ \texttt{=} $e_{i_1}$\texttt{;} \dots\texttt{;}
    $h_{i_m}$ \texttt{=} $e_{i_m}$ \texttt{\rb}},
\end{displaymath}
where the instance methods $h_{i_1}, \dots, h_{i_m}$ are a subset of
the methods $f_1, \dots, f_n$ declared for class $C$, a global
function
\begin{displaymath}
  \mbox{$f$ $d_1$ $\dots\;d_o$ \texttt{=} $C'$ $f'_1$ $\dots\;f'_n$},
\end{displaymath}
where $f=\emph{instFunId}(C,T)$ and $C'=\emph{dictConstrId}(C)$ is
added to the source code and its type is recorded in the type
environment. The function receives a dictionary argument for each of
the type predicates $C_i\,u_i$ appearing in the instance context
similar to the transformation of overloaded functions (see below). In
addition, a global function $f'_i$ is defined for each method $f_i$ of
class $C$, where
\begin{displaymath}
  f'_i =
    \left\{
      \begin{array}{ll}
        h_i & \mbox{if $i \in \left\{ i_1, \dots, i_m \right\}$,} \\
        \overline{f}_i & \mbox{otherwise,}
      \end{array}
    \right.
\end{displaymath}
and $\overline{f}_i'$ is the name of the default method implementation
of method $f_i$ in class $C$.
\begin{verbatim}

> bindInstDecls :: ModuleIdent -> TCEnv -> InstEnv -> ValueEnv -> ValueEnv
> bindInstDecls m tcEnv iEnv tyEnv =
>   foldr (bindInstFuns m tcEnv) tyEnv (envToList iEnv)

> bindInstFuns :: ModuleIdent -> TCEnv -> (CT,InstInfo) -> ValueEnv -> ValueEnv
> bindInstFuns m tcEnv (CT cls tc,(m',cx,fs)) tyEnv =
>   bindInstDict m cls ty m' cx $
>   foldr (bindInstMethod m tyEnv cls ty m' cx fs . fst) tyEnv
>         (classMethods cls tcEnv)
>   where ty = applyType (TypeConstructor tc) (take n (map TypeVariable [0..]))
>         n = kindArity (constrKind tc tcEnv) - kindArity (classKind cls tcEnv)

> bindInstDict :: ModuleIdent -> QualIdent -> Type -> ModuleIdent -> Context
>              -> ValueEnv -> ValueEnv
> bindInstDict m cls ty m' cx =
>   bindMethod m (qInstFunId m' cls ty) 0 (qualDictType cx (TypePred cls ty))

> bindInstMethod :: ModuleIdent -> ValueEnv -> QualIdent -> Type -> ModuleIdent
>                -> Context -> MethodList -> Ident -> ValueEnv -> ValueEnv
> bindInstMethod m tyEnv cls ty m' cx fs f =
>   bindMethod m (qInstMethodId m' cls ty f) (fromMaybe 0 (lookup f fs))
>              (instMethodType tyEnv cx cls ty f)

> bindMethod :: ModuleIdent -> QualIdent -> Int -> QualType -> ValueEnv
>            -> ValueEnv
> bindMethod m f n ty = bindEntity m f (Value f n (typeScheme ty))

> instExports :: ModuleIdent -> TCEnv -> QualIdent -> Type -> [Export]
> instExports m tcEnv cls ty =
>   Export (qInstFunId m cls ty) :
>   map (Export . qInstMethodId m cls ty . fst) (classMethods cls tcEnv)

> instDecls :: ModuleIdent -> TCEnv -> ValueEnv -> Position -> QualIdent
>           -> QualType -> [Decl QualType] -> [TopDecl QualType]
> instDecls m tcEnv tyEnv p cls (QualType cx ty) ds =
>   instDictDecl m tcEnv tyEnv p cx cls ty fs :
>   map (instMethodDecl tyEnv p cx cls ty (methodMap ds) . fst) fs
>   where fs = classMethods cls tcEnv

> instDictDecl :: ModuleIdent -> TCEnv -> ValueEnv -> Position -> Context
>              -> QualIdent -> Type -> MethodList -> TopDecl QualType
> instDictDecl m tcEnv tyEnv p cx cls ty fs =
>   functDecl p ty' (instFunId cls ty) [] (dictExpr m tcEnv tyEnv cls ty fs)
>   where ty' = QualType cx (arrowBase (instDictType tcEnv tyEnv cls ty fs))

> instMethodDecl :: ValueEnv -> Position -> Context -> QualIdent -> Type
>                -> [(Ident,Decl QualType)] -> Ident -> TopDecl QualType
> instMethodDecl tyEnv p cx cls ty ds f =
>   methodDecl (qDefaultMethodId cls f) p (instMethodId cls ty f) ty'
>              (lookup f ds)
>   where ty' = instMethodType tyEnv cx cls ty f

> methodDecl :: QualIdent -> Position -> Ident -> QualType
>            -> Maybe (Decl QualType) -> TopDecl QualType
> methodDecl _ _ f _ (Just (FunctionDecl p ty _ eqs)) =
>   BlockDecl (FunctionDecl p ty f (map (rename f) eqs))
>   where rename f (Equation p (FunLhs _ ts) rhs) = Equation p (FunLhs f ts) rhs
> methodDecl f0 p f ty Nothing =
>   functDecl p ty f [] (Variable (qualType (instType (unqualType ty))) f0)

> instDictType :: TCEnv -> ValueEnv -> QualIdent -> Type -> MethodList -> Type
> instDictType tcEnv tyEnv cls ty fs =
>   instanceType ty (unqualType (classDictType tcEnv tyEnv cls fs))

> instMethodType :: ValueEnv -> Context -> QualIdent -> Type -> Ident
>                -> QualType
> instMethodType tyEnv cx cls ty f = contextMap (cx ++) $
>   instanceType ty (contextMap tail (classMethodType tyEnv cls f))

> dictExpr :: ModuleIdent -> TCEnv -> ValueEnv -> QualIdent -> Type
>          -> MethodList -> Expression QualType
> dictExpr m tcEnv tyEnv cls ty fs =
>   apply (Constructor (qualType ty') (qDictConstrId cls))
>         (zipWith (Variable . qualType) (arrowArgs ty') fs')
>   where ty' = instType (instDictType tcEnv tyEnv cls ty fs)
>         fs' = map (qInstMethodId m cls ty . fst) fs

> methodMap :: [Decl a] -> [(Ident,Decl a)]
> methodMap ds = [(unRenameIdent f,d) | d@(FunctionDecl _ _ f _) <- ds]

\end{verbatim}
\paragraph{Trust Annotations}
Method implementations are lifted to the top-level effectively by
renaming them (see \texttt{methodDecl} above). In order to facilitate
debugging of method implementations, this renaming must be applied to
the trust annotation environment as well.
\begin{verbatim}

> liftTrustAnnots :: ModuleIdent -> TopDecl QualType -> TrustEnv -> TrustEnv
> liftTrustAnnots _ (DataDecl _ _ _ _ _ _) trEnv = trEnv
> liftTrustAnnots _ (NewtypeDecl _ _ _ _ _ _) trEnv = trEnv
> liftTrustAnnots _ (TypeDecl _ _ _ _) trEnv = trEnv
> liftTrustAnnots m (ClassDecl _ _ cls _ ds) trEnv =
>   foldr (liftMethodAnnot (defaultMethodId (qualifyWith m cls))) trEnv
>         [f | FunctionDecl _ _ f _ <- ds]
> liftTrustAnnots _ (InstanceDecl _ _ cls ty ds) trEnv =
>   foldr (liftMethodAnnot (instMethodId cls (toType [] ty))) trEnv
>         [f | FunctionDecl _ _ f _ <- ds]
> liftTrustAnnots _ (DefaultDecl _ _) trEnv = trEnv
> liftTrustAnnots _ (BlockDecl _) trEnv = trEnv

> liftMethodAnnot :: (Ident -> Ident) -> Ident -> TrustEnv -> TrustEnv
> liftMethodAnnot methodId f trEnv =
>   case lookupEnv f trEnv of
>     Just tr -> bindEnv (methodId f) tr (unbindEnv f trEnv)
>     Nothing -> trEnv

\end{verbatim}
\paragraph{Adding Dictionary Arguments}
Given a function $f$ with type $(C_1\,u_1, \dots, C_n\,u_n)
\Rightarrow \tau$, the compiler adds $n$ implicit dictionary arguments
to the function's declaration thereby changing $f$'s type into
$T_1\,u_1 \rightarrow \dots \rightarrow T_n\,u_n \rightarrow \tau$,
where $T_i=\emph{dictTypeId}(C_i)$. The types of these variables are
recorded in the type environment. Furthermore, an association list is
computed that maps the constraints $C_i\,u_i$ and the corresponding
super class constraints onto the respective dictionary arguments and
expressions that return the super class dictionaries for them. This
association list is used when transforming function applications in
$f$'s body. Note that the list is carefully ordered so as to minimize
the number of applications required to compute the dictionary of a
class $C'$ that is a super class of two or more of the classes $C_1,
\dots, C_n$.

A data constructor definition
\begin{displaymath}
  \begin{array}{l}
    \mbox{\texttt{data} $(C_{i_1}\,u_{i_1},\dots,C_{i_l}\,u_{i_l})$
      \texttt{=>} $T\,u_1 \dots u_n$ \texttt{=}} \\
    \mbox{\quad\dots{} \texttt{|} \texttt{forall} $u_{n+1} \dots u_m$
      \texttt{.} $(C_{j_1}\,u_{j_1},\dots,C_{j_r}\,u_{j_r})$
      \texttt{=>} $\tau_1 \dots \tau_k$ \texttt{|} \dots}
  \end{array}
\end{displaymath}
is changed into
\begin{displaymath}
  \begin{array}{l}
    \mbox{\texttt{data} $T\,u_1 \dots u_n$ \texttt{=}} \\
    \mbox{\quad\dots{} \texttt{|} \texttt{forall} $u_{n+1} \dots u_m$
      \texttt{.} $(T_{j_1}\,u_{j_1}) \dots (T_{j_r}\,u_{j_r}) \;
      \tau_1 \dots \tau_k$ \texttt{|} \dots}
  \end{array}
\end{displaymath}
where $T_j = \emph{dictTypeId}(C_j)$, and implicit dictionary arguments
are added to all occurrences of $C$ in patterns.

The pattern declaration case of the \texttt{DictTrans} \texttt{Decl}
instance converts variable declarations with an overloaded type into
function declarations. This is necessary so that the compiler can add
the implicit dictionary arguments to the declaration.
\begin{verbatim}

> type DictEnv = [(TypePred,Expression Type)]

> dictTransValues :: ValueEnv -> ValueEnv
> dictTransValues = fmap transInfo
>   where transInfo (DataConstructor c ls ci (ForAll n ty)) =
>           DataConstructor c ls' (constrInfo ci) (ForAll n (qualType ty'))
>           where ty' = transformConstrType ci ty
>                 ls' = replicate (arrowArity ty' - length ls) anonId ++ ls
>                 constrInfo (ConstrInfo n _) = ConstrInfo n []
>         transInfo (NewtypeConstructor c l ty) =
>           NewtypeConstructor c l (tmap (qualType . unqualType) ty)
>         transInfo (Value f n ty) = Value f n' ty'
>           where n' = n + arrowArity (rawType ty') - arrowArity (rawType ty)
>                 ty' = tmap (qualType . transformType) ty

> transformConstrType :: ConstrInfo -> QualType -> Type
> transformConstrType ci ty = transformType (constrTypeRhs ci ty)

> class DictTrans a where
>   dictTrans :: TCEnv -> InstEnv -> ValueEnv -> DictEnv -> a QualType
>             -> DictState (a Type)

> instance DictTrans TopDecl where
>   dictTrans tcEnv iEnv tyEnv dictEnv (DataDecl p cxL tc tvs cs clss) =
>     return (DataDecl p [] tc tvs (map dictTransConstrDecl cs) clss)
>     where dictTransConstrDecl (ConstrDecl p evs cxR c tys) =
>             ConstrDecl p evs [] c $
>             map (fromType (tvs ++ evs)) . arrowArgs $
>             uncurry transformConstrType $
>             expandConstrType tcEnv cxL (qualify tc) tvs cxR tys
>   dictTrans _ _ _ _ (NewtypeDecl p cx tc tvs nc clss) =
>     return (NewtypeDecl p [] tc tvs nc clss)
>   dictTrans _ _ _ _ (TypeDecl p tc tvs ty) = return (TypeDecl p tc tvs ty)
>   dictTrans tcEnv iEnv tyEnv dictEnv (BlockDecl d) =
>     liftM BlockDecl (dictTrans tcEnv iEnv tyEnv dictEnv d)

> instance DictTrans Decl where
>   dictTrans _ _ _ _ (InfixDecl p fix pr ops) = return (InfixDecl p fix pr ops)
>   dictTrans tcEnv _ _ _ (TypeSig p fs ty) =
>     return (TypeSig p fs (QualTypeExpr [] ty'))
>     where ty' = fromType nameSupply (transformType (expandPolyType tcEnv ty))
>   dictTrans tcEnv iEnv tyEnv dictEnv (FunctionDecl p ty f eqs) =
>     liftM (FunctionDecl p (transformType ty) f)
>           (mapM (dictTrans tcEnv iEnv tyEnv dictEnv) eqs)
>   dictTrans _ _ _ _ (ForeignDecl p fi ty f ty') =
>     return (ForeignDecl p fi (unqualType ty) f ty')
>   dictTrans tcEnv iEnv tyEnv dictEnv (PatternDecl p t rhs) =
>     case t of
>       VariablePattern (QualType cx ty) v
>         | not (null cx) ->
>             dictTrans tcEnv iEnv tyEnv dictEnv $
>             FunctionDecl p (QualType cx ty) v [Equation p (FunLhs v []) rhs]
>       _ ->
>         do
>           (dictEnv',t') <- dictTransTerm tcEnv tyEnv dictEnv t
>           rhs' <- dictTrans tcEnv iEnv tyEnv dictEnv' rhs
>           return (PatternDecl p t' rhs')
>   dictTrans _ _ _ _ (FreeDecl p vs) =
>     return (FreeDecl p (map (fmap unqualType) vs))
>   dictTrans _ _ _ _ (TrustAnnot p tr fs) = return (TrustAnnot p tr fs)

> instance DictTrans Equation where
>   dictTrans tcEnv iEnv tyEnv dictEnv (Equation p (FunLhs f ts) rhs) =
>     do
>       (dictEnv',ts') <- addDictArgs tcEnv tyEnv dictEnv cx ts
>       rhs' <- dictTrans tcEnv iEnv (bindTerms ts' tyEnv) dictEnv' rhs
>       return (Equation p (FunLhs f ts') rhs')
>     where cx = matchContext tcEnv (varType f tyEnv) $
>                foldr (TypeArrow . typeOf) (typeOf rhs) ts

> instance DictTrans Rhs where
>   dictTrans tcEnv iEnv tyEnv dictEnv (SimpleRhs p e ds) =
>     liftM2 (SimpleRhs p)
>            (dictTrans tcEnv iEnv tyEnv' dictEnv e)
>            (mapM (dictTrans tcEnv iEnv tyEnv' dictEnv) ds)
>     where tyEnv' = bindDecls ds tyEnv

> addDictArgs :: TCEnv -> ValueEnv -> DictEnv -> Context
>             -> [ConstrTerm QualType] -> DictState (DictEnv,[ConstrTerm Type])
> addDictArgs tcEnv tyEnv dictEnv cx ts =
>   do
>     xs <- mapM (freshVar "_#dict" . dictType) cx
>     let dictEnv' = dicts (zip cx (map (uncurry mkVar) xs)) ++ dictEnv
>     (dictEnv'',ts') <- mapAccumM (dictTransTerm tcEnv tyEnv) dictEnv' ts
>     return (dictEnv'',map (uncurry VariablePattern) xs ++ ts')
>   where dicts ds
>           | null ds = ds
>           | otherwise = ds ++ dicts (concatMap superDicts ds)
>         superDicts (TypePred cls ty,e) =
>           map (superDict cls ty e) (superClasses cls tcEnv)
>         superDict cls ty e cls' =
>           (TypePred cls' ty,Apply (superDictExpr cls cls' ty) e)
>         superDictExpr cls super ty =
>           Variable (superDictType cls super ty) (qSuperDictId cls super)

\end{verbatim}
An application of an overloaded function $f$ with type $(C_1\,u_1,
\dots, C_n\,u_n) \Rightarrow \tau$ is changed into an application of
$f$ to the dictionaries for $C_1\,\tau_1, \dots, C_n\,\tau_n$ where
the types $\tau_i$ are given by $\tau_i = \theta u_i$ where $\theta$
is the most general unifier between $f$'s type $\tau$ and the concrete
type at which $f$ is used in the application. An application of a data
constructor with a non-empty right hand side context is changed
similarly.
\begin{verbatim}

> instance DictTrans Expression where
>   dictTrans _ _ _ _ (Literal ty l) = return (Literal (unqualType ty) l)
>   dictTrans tcEnv iEnv tyEnv dictEnv (Variable ty v) =
>     return (apply (Variable ty' v) xs)
>     where ty' = foldr (TypeArrow . typeOf) (unqualType ty) xs
>           xs = map (dictArg iEnv dictEnv) cx
>           cx = matchContext tcEnv (funType v tyEnv) (unqualType ty)
>   dictTrans tcEnv iEnv tyEnv dictEnv (Constructor ty c) =
>     return (apply (Constructor ty' c) xs)
>     where ty' = foldr (TypeArrow . typeOf) (unqualType ty) xs
>           xs = map (dictArg iEnv dictEnv) cx
>           cx = matchContext tcEnv (conTypeRhs c tyEnv) (unqualType ty)
>   dictTrans tcEnv iEnv tyEnv dictEnv (Apply e1 e2) =
>     liftM2 Apply
>            (dictTrans tcEnv iEnv tyEnv dictEnv e1)
>            (dictTrans tcEnv iEnv tyEnv dictEnv e2)
>   dictTrans tcEnv iEnv tyEnv dictEnv (Lambda p ts e) =
>     do
>       (dictEnv',ts') <- mapAccumM (dictTransTerm tcEnv tyEnv) dictEnv ts
>       e' <- dictTrans tcEnv iEnv (bindTerms ts' tyEnv) dictEnv' e
>       return (Lambda p ts' e')
>   dictTrans tcEnv iEnv tyEnv dictEnv (Let ds e) =
>     liftM2 Let
>            (mapM (dictTrans tcEnv iEnv tyEnv' dictEnv) ds)
>            (dictTrans tcEnv iEnv tyEnv' dictEnv e)
>     where tyEnv' = bindDecls ds tyEnv
>   dictTrans tcEnv iEnv tyEnv dictEnv (Case e as) =
>     liftM2 Case
>            (dictTrans tcEnv iEnv tyEnv dictEnv e)
>            (mapM (dictTrans tcEnv iEnv tyEnv dictEnv) as)
>   dictTrans tcEnv iEnv tyEnv dictEnv (Fcase e as) =
>     liftM2 Fcase
>            (dictTrans tcEnv iEnv tyEnv dictEnv e)
>            (mapM (dictTrans tcEnv iEnv tyEnv dictEnv) as)

> instance DictTrans Alt where
>   dictTrans tcEnv iEnv tyEnv dictEnv (Alt p t rhs) =
>     do
>       (dictEnv',t') <- dictTransTerm tcEnv tyEnv dictEnv t
>       rhs' <- dictTrans tcEnv iEnv (bindTerm t' tyEnv) dictEnv' rhs
>       return (Alt p t' rhs')

> dictTransTerm :: TCEnv -> ValueEnv -> DictEnv -> ConstrTerm QualType
>               -> DictState (DictEnv,ConstrTerm Type)
> dictTransTerm _ _ dictEnv (LiteralPattern ty l) =
>   return (dictEnv,LiteralPattern (unqualType ty) l)
> dictTransTerm _ _ dictEnv (VariablePattern ty v) =
>   return (dictEnv,VariablePattern (unqualType ty) v)
> dictTransTerm tcEnv tyEnv dictEnv (ConstructorPattern ty c ts) =
>   do
>     (dictEnv',ts') <- addDictArgs tcEnv tyEnv dictEnv cx ts
>     return (dictEnv',ConstructorPattern (unqualType ty) c ts')
>   where cx = matchContext tcEnv (conTypeRhs c tyEnv) $
>              foldr (TypeArrow . typeOf) (unqualType ty) ts
> dictTransTerm tcEnv tyEnv dictEnv (AsPattern v t) =
>   do
>     (dictEnv',t') <- dictTransTerm tcEnv tyEnv dictEnv t
>     return (dictEnv',AsPattern v t')

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
  possible. For instance, just one \texttt{Eq} \texttt{Int} dictionary
  should be created for the expression
  \texttt{elem (x::Int) xs \&\& elem x ys}.}
\begin{verbatim}

> dictArg :: InstEnv -> DictEnv -> TypePred -> Expression Type
> dictArg iEnv dictEnv tp =
>   fromMaybe (instDict iEnv dictEnv tp) (lookup tp dictEnv)

> instDict :: InstEnv -> DictEnv -> TypePred -> Expression Type
> instDict iEnv dictEnv tp = instFunApp iEnv dictEnv (instContext iEnv tp) tp

> instFunApp :: InstEnv -> DictEnv -> (ModuleIdent,Context) -> TypePred
>            -> Expression Type
> instFunApp iEnv dictEnv (m,cx) (TypePred cls ty) =
>   apply (Variable ty' (qInstFunId m cls ty)) (map (dictArg iEnv dictEnv) cx)
>   where ty' = transformType (qualDictType cx (TypePred cls ty))

> instContext :: InstEnv -> TypePred -> (ModuleIdent,Context)
> instContext iEnv (TypePred cls ty) =
>   case unapplyType True ty of
>     (TypeConstructor tc,tys) ->
>       case lookupEnv (CT cls tc) iEnv of
>         Just (m,cx,_) -> (m,map (expandAliasType tys) cx)
>         Nothing ->
>           internalError ("instContext " ++ show cls ++ " " ++ show tc)
>     _ ->
>       internalError ("instContext " ++ show cls ++ " " ++ showsPrec 11 ty "")

> transformType :: QualType -> Type
> transformType (QualType cx ty) = foldr (TypeArrow . dictType) ty cx

\end{verbatim}
\paragraph{Optimizing method calls}
When a type class method is applied at a known type, the compiler can
apply the type instance's implementation directly. This improves
performance considerably for a lot of examples. Therefore, the
compiler looks for applications of method stubs at a fixed type in
the transformed code and replaces them by applications of the
corresponding instance methods.

The dictionary transformation so far has replaced each occurrence of a
method $f$ from class $C$ by an application $f\,d$, where $d$ is an
expression returning a suitable dictionary for the instance of $C$ at
the type where the method is used (cf.\ the code of function
\texttt{methodStubs} above). Since only single parameter classes are
allowed, the dictionary expression $d$ must have a type of the form
$D\,\tau$, where $D$ is the dictionary type constructor corresponding
to $C$ and $\tau$ is the type of the instance at which the method is
used.

In order to specialize method calls, we construct an environment that
maps pairs of all method names and instance dictionary functions onto
the names of the respective instance method implementations. For the
sake of a more efficient implementation, this environment is really
implemented as an environment from method names to association lists,
which map instance dictionary functions onto instance method names.
\label{dict-specialize}
\begin{verbatim}

> type MethodEnv = Env QualIdent [(QualIdent,QualIdent)]

> dictSpecializeModule :: TCEnv -> InstEnv -> Module Type -> Module Type
> dictSpecializeModule tcEnv iEnv (Module m es is ds) =
>   Module m es is (map (dictSpecialize (methodEnv tcEnv iEnv)) ds)

> methodEnv :: TCEnv -> InstEnv -> MethodEnv
> methodEnv tcEnv iEnv = foldr (uncurry bindInstance) emptyEnv (envToList iEnv)
>   where bindInstance (CT cls tc) (m,_,_) mEnv =
>           foldr (bindMethod m cls ty . fst) mEnv (classMethods cls tcEnv)
>           where ty = TypeConstructor tc {-cheating!-}
>         bindMethod m cls ty f mEnv =
>           bindEnv f' ((d,f'') : fromMaybe [] (lookupEnv f' mEnv)) mEnv
>           where f' = qualifyLike cls f
>                 d = qInstFunId m cls ty
>                 f'' = qInstMethodId m cls ty f

> class DictSpecialize a where
>   dictSpecialize :: MethodEnv -> a Type -> a Type

> instance DictSpecialize TopDecl where
>   dictSpecialize _ (DataDecl p cx tc tvs cs clss) =
>     DataDecl p cx tc tvs cs clss
>   dictSpecialize _ (NewtypeDecl p cx tc tvs nc clss) =
>     NewtypeDecl p cx tc tvs nc clss
>   dictSpecialize _ (TypeDecl p tc tvs ty) = TypeDecl p tc tvs ty
>   dictSpecialize _ (DefaultDecl p tys) = DefaultDecl p tys
>   dictSpecialize mEnv (BlockDecl d) = BlockDecl (dictSpecialize mEnv d)

> instance DictSpecialize Decl where
>   dictSpecialize _ (InfixDecl p fix pr ops) = InfixDecl p fix pr ops
>   dictSpecialize _ (TypeSig p fs ty) = TypeSig p fs ty
>   dictSpecialize mEnv (FunctionDecl p ty f eqs) =
>     FunctionDecl p ty f (map (dictSpecialize mEnv) eqs)
>   dictSpecialize _ (ForeignDecl p fi ty f ty') = ForeignDecl p fi ty f ty'
>   dictSpecialize mEnv (PatternDecl p t rhs) =
>     PatternDecl p t (dictSpecialize mEnv rhs)
>   dictSpecialize _ (FreeDecl p vs) = FreeDecl p vs
>   dictSpecialize _ (TrustAnnot p tr fs) = TrustAnnot p tr fs

> instance DictSpecialize Equation where
>   dictSpecialize mEnv (Equation p lhs rhs) =
>     Equation p lhs (dictSpecialize mEnv rhs)

> instance DictSpecialize Rhs where
>   dictSpecialize mEnv (SimpleRhs p e _) =
>     SimpleRhs p (dictSpecialize mEnv e) []

> instance DictSpecialize Expression where
>   dictSpecialize mEnv e = dictSpecializeApp mEnv e []

> instance DictSpecialize Alt where
>   dictSpecialize mEnv (Alt p t rhs) = Alt p t (dictSpecialize mEnv rhs)

\end{verbatim}
When we change an application of a method stub $f$ from class $C$ into
an application of the corresponding instance method $f'$ for type
$\tau$, we must be careful to apply the instance method to the same
dictionaries as its instance creation function.
\begin{verbatim}

> dictSpecializeApp :: MethodEnv -> Expression Type -> [Expression Type]
>                   -> Expression Type
> dictSpecializeApp _ (Literal ty l) es = apply (Literal ty l) es
> dictSpecializeApp mEnv (Variable ty v) es =
>   case lookupEnv v mEnv of
>     Just fs ->
>       case lookup f' fs of
>         Just f'' -> apply (Variable ty'' f'') (es'' ++ es')
>         Nothing -> apply (Variable ty v) es
>       where d:es' = es
>             (Variable _ f',es'') = unapply d []
>             ty'' = foldr (TypeArrow . typeOf) (typeOf e) es''
>             e = Apply (Variable ty v) d
>     Nothing -> apply (Variable ty v) es
> dictSpecializeApp _ (Constructor ty c) es = apply (Constructor ty c) es
> dictSpecializeApp mEnv (Apply e1 e2) es =
>   dictSpecializeApp mEnv e1 (dictSpecialize mEnv e2 : es)
> dictSpecializeApp mEnv (Lambda p ts e) es =
>   apply (Lambda p ts (dictSpecialize mEnv e)) es
> dictSpecializeApp mEnv (Let ds e) es =
>   apply (Let (map (dictSpecialize mEnv) ds) (dictSpecialize mEnv e)) es
> dictSpecializeApp mEnv (Case e as) es =
>   apply (Case (dictSpecialize mEnv e) (map (dictSpecialize mEnv) as)) es
> dictSpecializeApp mEnv (Fcase e as) es =
>   apply (Fcase (dictSpecialize mEnv e) (map (dictSpecialize mEnv) as)) es

> unapply :: Expression a -> [Expression a] -> (Expression a,[Expression a])
> unapply (Literal ty l) es = (Literal ty l,es)
> unapply (Variable ty x) es = (Variable ty x,es)
> unapply (Constructor ty c) es = (Constructor ty c,es)
> unapply (Apply e1 e2) es = unapply e1 (e2:es)
> unapply (Lambda p ts e) es = (Lambda p ts e,es)
> unapply (Let ds e) es = (Let ds e,es)
> unapply (Case e as) es = (Case e as,es)
> unapply (Fcase e as) es = (Fcase e as,es)

\end{verbatim}
\paragraph{Unification}
When adding dictionary arguments on the left hand side of an equation
and in applications, respectively, the compiler must unify the
function's type with the concrete instance at which that type is used
in order to determine the correct context. This problem does not
require a general unification because only the polymorphic type
variables of the function's type can be instantiated to a particular
monomorphic type.

Polymorphic methods make things a little bit more complicated. When an
instance dictionary constructor is applied to an instance method, the
suffix of the instance method type's context that corresponds to the
additional constraints of the type class method must be discarded and
no dictionaries must be added for these constraints. Unfortunately,
the dictionary transformation has already been applied to the
component types of the dictionary constructor. Therefore,
\texttt{matchContext} tries to find a suffix of the context whose
transformation matches the initial arrows of the instance type.
\begin{verbatim}

> matchContext :: TCEnv -> TypeScheme -> Type -> Context
> matchContext tcEnv (ForAll _ (QualType cx ty1)) ty2 =
>   foldr (\(cx1,cx2) cx' -> fromMaybe cx' (qualMatch tcEnv cx1 ty1 cx2 ty2))
>         (internalError "matchContext")
>         (splits cx)

> qualMatch :: TCEnv -> Context -> Type -> Context -> Type -> Maybe Context
> qualMatch tcEnv cx1 ty1 cx2 ty2 =
>   case contextMatch cx2 ty2 of
>     Just ty2' -> Just (subst (matchType tcEnv ty1 ty2' idSubst) cx1)
>     Nothing -> Nothing

> contextMatch :: Context -> Type -> Maybe Type
> contextMatch [] ty = Just ty
> contextMatch (tp:cx) ty =
>   case ty of
>     TypeArrow ty1 ty2
>       | ty1 == dictType (instTypePred tp) -> contextMatch cx ty2
>     _ -> Nothing

> splits :: [a] -> [([a],[a])]
> splits [] = [([],[])]
> splits (x:xs) = ([],x:xs) : [(x:ys,zs) | (ys,zs) <- splits xs]

\end{verbatim}
\paragraph{Auxiliary Functions}
The functions \texttt{dictTypeId} and \texttt{dictConstrId} return the
names of the dictionary type and data constructors for a class,
respectively. For simplicity, we use the same identifier for the
dictionary type and its data constructor. The functions
\texttt{qDictTypeId} and \texttt{qDictConstrId} are variants of these
functions that transform qualified names.
\begin{verbatim}

> dictTypeId :: QualIdent -> Ident
> dictTypeId cls = mkIdent ("_Dict#" ++ name (unqualify cls))

> qDictTypeId :: QualIdent -> QualIdent
> qDictTypeId cls = qualifyLike cls (dictTypeId cls)

> dictConstrId :: QualIdent -> Ident
> dictConstrId = dictTypeId

> qDictConstrId :: QualIdent -> QualIdent
> qDictConstrId = qDictTypeId

\end{verbatim}
The functions \texttt{defaultMethodId} and \texttt{qDefaultMethodId}
return the (qualified) name of a lifted default type class method.
\begin{verbatim}

> defaultMethodId :: QualIdent -> Ident -> Ident
> defaultMethodId cls f = mkIdent (name f ++ '#' : qualName cls)

> qDefaultMethodId :: QualIdent -> Ident -> QualIdent
> qDefaultMethodId cls = qualifyLike cls . defaultMethodId cls

\end{verbatim}
The functions \texttt{superDictId} and \texttt{qSuperDictId} return
the (qualified) name of the global function which returns a super
class dictionary from the dictionary of a class. The first argument is
the name of the class and the second the name of its super class. Note
that constructing these names in the same way as those of the
functions returning the dictionary of a particular C-T instance is
safe because type constructors and type classes share a common name
space.
\begin{verbatim}

> superDictId :: QualIdent -> QualIdent -> Ident
> superDictId cls super = instFunId super (TypeConstructor cls)

> qSuperDictId :: QualIdent -> QualIdent -> QualIdent
> qSuperDictId cls = qualifyLike cls . superDictId cls

\end{verbatim}
The functions \texttt{instFunId} and \texttt{qInstFunId} return the
(qualified) name of the global function which returns the dictionary
for a particular C-T instance pair.
\begin{verbatim}

> instFunId :: QualIdent -> Type -> Ident
> instFunId cls ty =
>   mkIdent ("_inst#" ++ qualName cls ++ '#' : qualName (rootOfType ty))

> qInstFunId :: ModuleIdent -> QualIdent -> Type -> QualIdent
> qInstFunId m cls = qualifyWith m . instFunId cls

\end{verbatim}
The functions \texttt{instMethodId} and \texttt{qInstMethodId} return
the (qualified) name of a lifted type class instance method.
\begin{verbatim}

> instMethodId :: QualIdent -> Type -> Ident -> Ident
> instMethodId cls ty = instMethodId' cls (rootOfType ty)
>   where instMethodId' cls tc f =
>           mkIdent (name f ++ '#' : qualName cls ++ '#' : qualName tc)

> qInstMethodId :: ModuleIdent -> QualIdent -> Type -> Ident -> QualIdent
> qInstMethodId m cls ty = qualifyWith m . instMethodId cls ty

\end{verbatim}
The functions \texttt{dictType} and \texttt{qualDictType} return the
(qualified) type of the dictionary corresponding to a particular
$C$-$T$ instance.
\begin{verbatim}

> dictType :: TypePred -> Type
> dictType (TypePred cls ty) = TypeApply (TypeConstructor (qDictTypeId cls)) ty

> qualDictType :: Context -> TypePred -> QualType
> qualDictType cx tp = QualType cx (dictType tp)

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
>   case splitQualIdent (qualUnqualify m x) of
>     (Just _,_) -> qualImportTopEnv x
>     (Nothing,x') -> globalBindTopEnv m x'

\end{verbatim}
The monad transformer \texttt{freshVar} returns a new identifier and
records it in the type environment.
\begin{verbatim}

> freshVar :: String -> Type -> DictState (Type,Ident)
> freshVar prefix ty =
>   do
>     v <- liftM mkName (updateSt (1 +))
>     return (ty,v)
>   where mkName n = renameIdent (mkIdent (prefix ++ show n)) n

\end{verbatim}
The functions \texttt{constrTypeRhs} and \texttt{conTypeRhs} return
the type (scheme) of a data constructor with the context restricted to
only those predicates which appear on the right hand side of its
declaration.
\begin{verbatim}

> constrTypeRhs :: ConstrInfo -> QualType -> QualType
> constrTypeRhs (ConstrInfo _ cxR) (QualType _ ty) = QualType cxR ty

> conTypeRhs :: QualIdent -> ValueEnv -> TypeScheme
> conTypeRhs c tyEnv = tmap (constrTypeRhs ci) ty
>   where (_,ci,ty) = conType c tyEnv

\end{verbatim}
Convenience functions for constructing parts of the syntax tree.
\begin{verbatim}

> functDecl :: Position -> a -> Ident -> [ConstrTerm a] -> Expression a
>           -> TopDecl a
> functDecl p ty f ts e = BlockDecl $ funDecl p ty f ts e

\end{verbatim}
Prelude entities.
\begin{verbatim}

> qUndefinedId :: QualIdent
> qUndefinedId = qualifyWith preludeMIdent (mkIdent "undefined")

\end{verbatim}
