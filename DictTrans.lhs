% -*- LaTeX -*-
% $Id: DictTrans.lhs 2507 2007-10-16 22:24:05Z wlux $
%
% Copyright (c) 2006-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{DictTrans.lhs}
\section{Introducing Dictionaries}\label{sec:dict-trans}
For the implementation of type classes, we follow the common approach
to use dictionaries~\cite{PetersonJones93:TypeClasses}. For every type
predicate in the context of a function's type we introduce an implicit
dictionary argument. For the purpose of introducing dictionaries, the
compiler expands contexts by adding all implied type predicates. Thus,
dictionaries for all classes and their super classes are immediately
available as function arguments in the transformed code. The
dictionaries themselves are derived from the type class and instance
declarations in the module.
\begin{verbatim}

> module DictTrans(dictTransModule, dictTransInterface,
>                  dictSpecializeModule) where
> import Base
> import Combined
> import Curry
> import CurryUtils
> import Env
> import Kinds
> import List
> import Maybe
> import Monad
> import PredefIdent
> import TopEnv
> import Types
> import TypeSubst
> import TypeTrans
> import Typing
> import Utils

\end{verbatim}
In order to generate unique names for the implicit dictionary
arguments and add their types to the type environment, we use a nested
state monad.
\begin{verbatim}

> type DictState a = StateT ValueEnv (StateT Int Id) a

> run :: DictState a -> ValueEnv -> a
> run m tyEnv = runSt (callSt m tyEnv) 1

\end{verbatim}
The introduction of dictionaries proceeds in three phases. In the
first phase, the compiler adds data type declarations for the
dictionary constructors to the source code, introduces new top-level
functions for creating instance dictionaries, and lifts class and
instance method implementations to the top-level.

Lifting default class method implementations is necessary so that the
compiler can use them in place of omitted instance methods. Lifting
instance method declarations allows calling methods directly when a
method is applied at a known type, which can improve performance
considerably.

In the second phase, the compiler introduces dictionary arguments in
the left hand sides of overloaded function declarations and lifted
method declarations, and transforms occurrences of overloaded
functions and methods in expressions into applications to the
appropriate dictionary arguments.

In addition, the compiler introduces a method stub function for each
type class method that extracts the corresponding method implementation
from a dictionary.

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
\begin{verbatim}

> dictTransModule :: TCEnv -> InstEnv -> ValueEnv -> Module Type
>                 -> (TCEnv,ValueEnv,Module Type)
> dictTransModule tcEnv iEnv tyEnv (Module m es is ds) =
>   run (do
>          ds' <- mapM (dictTrans m tcEnv' nEnv iEnv tyEnv' emptyEnv)
>                      (concatMap (liftDecls m tcEnv tyEnv') ds)
>          dss <- mapM (methodStubs m tcEnv' tyEnv') ds
>          tyEnv'' <- fetchSt
>          return (tcEnv',tyEnv'',Module m es is (ds' ++ concat dss)))
>       (dictTransValues tcEnv' tyEnv')
>   where tcEnv' = bindDictTypes m tcEnv
>         tyEnv' = bindClassDecls m tcEnv' (bindInstDecls m tcEnv' iEnv tyEnv)
>         nEnv = newtypeEnv tyEnv

> liftDecls :: ModuleIdent -> TCEnv -> ValueEnv -> TopDecl Type
>           -> [TopDecl Type]
> liftDecls _ _ _ (DataDecl p cx tc tvs cs _) = [DataDecl p cx tc tvs cs []]
> liftDecls _ _ _ (NewtypeDecl p cx tc tvs nc _) =
>   [NewtypeDecl p cx tc tvs nc []]
> liftDecls _ _ _ (TypeDecl p tc tvs ty) = [TypeDecl p tc tvs ty]
> liftDecls _ tcEnv tyEnv (ClassDecl p _ cls tv ds) =
>   classDecls tcEnv tyEnv p cls tv ds
> liftDecls m tcEnv tyEnv (InstanceDecl p cx cls ty ds) =
>   instDecls m tcEnv tyEnv p cls (expandPolyType tcEnv (QualTypeExpr cx ty)) ds
> liftDecls _ _ _ (DefaultDecl p tys) = [DefaultDecl p tys]
> liftDecls _ _ _ (BlockDecl d) = [BlockDecl d]

\end{verbatim}
Besides the source code definitions, the compiler must also transform
the imported interface modules because their declarations are used to
supply the appropriate environment for the abstract machine code
generator.
\begin{verbatim}

> dictTransInterface :: TCEnv -> ValueEnv -> Interface -> Interface
> dictTransInterface tcEnv tyEnv (Interface m is ds) =
>   Interface m is (map (dictTransIntfDecl m tcEnv') dss)
>   where dss = concatMap (liftIntfDecls m tcEnv' tyEnv) ds
>         tcEnv' = bindDictTypes m tcEnv

> liftIntfDecls :: ModuleIdent -> TCEnv -> ValueEnv -> IDecl -> [IDecl]
> liftIntfDecls _ _ _ (IInfixDecl p fix pr op) = [IInfixDecl p fix pr op]
> liftIntfDecls _ _ _ (HidingDataDecl p tc k tvs) = [HidingDataDecl p tc k tvs]
> liftIntfDecls _ _ _ (IDataDecl p cx tc k tvs cs) =
>   [IDataDecl p cx tc k tvs cs]
> liftIntfDecls _ _ _ (INewtypeDecl p cx tc k tvs nc) =
>   [INewtypeDecl p cx tc k tvs nc]
> liftIntfDecls _ _ _ (ITypeDecl p tc k tvs ty) = [ITypeDecl p tc k tvs ty]
> liftIntfDecls m tcEnv _ (HidingClassDecl p _ cls k tv) =
>   classIDecls m tcEnv p cls k tv Nothing
> liftIntfDecls m tcEnv _ (IClassDecl p _ cls k tv ds) =
>   classIDecls m tcEnv p cls k tv (Just ds) ++ intfMethodStubs cls tv ds
> liftIntfDecls m tcEnv tyEnv (IInstanceDecl p cx cls ty m') =
>   instIDecls tcEnv tyEnv p cls' (toQualType m (QualTypeExpr cx ty)) m''
>   where cls' = qualQualify m cls
>         m'' = fromMaybe m m'
> liftIntfDecls _ _ _ (IFunctionDecl p f n ty) = [IFunctionDecl p f n ty]

> dictTransIntfDecl :: ModuleIdent -> TCEnv -> IDecl -> IDecl
> dictTransIntfDecl m tcEnv (IDataDecl p cxL tc k tvs cs) =
>   IDataDecl p [] tc k tvs (map (fmap dictTransConstrDecl) cs)
>   where dictTransConstrDecl (ConstrDecl p evs cxR c tys) =
>           dictTransConstrDecl' p evs cxR c tys
>         dictTransConstrDecl (ConOpDecl p evs cxR ty1 op ty2) =
>           dictTransConstrDecl' p evs cxR op [ty1,ty2]
>         dictTransConstrDecl' p evs cxR c tys = ConstrDecl p evs [] c tys'
>           where tys' = map (fromType tcEnv (tvs ++ evs)) . arrowArgs $
>                        uncurry (transformConstrType tcEnv) $
>                        toConstrType m cxL tc tvs cxR tys
> dictTransIntfDecl m tcEnv (INewtypeDecl p _ tc k tvs nc) =
>   INewtypeDecl p [] tc k tvs nc
> dictTransIntfDecl m tcEnv (IFunctionDecl p f n ty) =
>   IFunctionDecl p f (fmap (+ toInteger d) n)
>                 (fromQualType tcEnv (nub (fv ty)) (qualType ty''))
>   where ty' = toQualType m ty
>         ty'' = transformQualType tcEnv ty'
>         d = arrowArity ty'' - arrowArity (unqualType ty')
> dictTransIntfDecl _ _ d = d

> transformConstrType :: TCEnv -> ConstrInfo -> QualType -> Type
> transformConstrType tcEnv ci ty =
>   transformQualType tcEnv (constrTypeRhs ci ty)

> transformQualType :: TCEnv -> QualType -> Type
> transformQualType tcEnv = transformType . contextMap (maxContext tcEnv)

\end{verbatim}
\paragraph{Class Declarations}
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
environments are updated accordingly.

In case of polymorphic methods, we have to cheat a little bit, since
our type representation does not support polymorphic components. We
simply use the method types recorded in the type environment when
computing the type of a dictionary constructor. This means that the
methods' polymorphic type variables -- i.e., all type variables other
than the class' type variable -- are assigned indices greater than 0
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
to avoid name conflicts with the method names themselves. In order to
avoid problems with hidden methods, whose names are not available in
the interface files, the lifted names are derived from the class' name
and the methods' indices. If the user does not provide a default
implementation for a method, the compiler uses a default
implementation that is equivalent to \texttt{Prelude.undefined}.

\ToDo{Use \texttt{Prelude.error} instead of \texttt{Prelude.undefined}
  as default implementation for omitted methods?}
\begin{verbatim}

> bindDictTypes :: ModuleIdent -> TCEnv -> TCEnv
> bindDictTypes m tcEnv = foldr (bindDictType m) tcEnv (allEntities tcEnv)

> bindDictType :: ModuleIdent -> TypeInfo -> TCEnv -> TCEnv
> bindDictType m (TypeClass cls k _ _) =
>   bindEntity m tc (DataType tc (KindArrow k KindStar) [Just c])
>   where tc = qDictTypeId cls
>         c = dictConstrId (unqualify cls)
> bindDictType _ _ = id

> bindClassDecls :: ModuleIdent -> TCEnv -> ValueEnv -> ValueEnv
> bindClassDecls m tcEnv tyEnv =
>   foldr (bindClassEntities m tcEnv) tyEnv (allEntities tcEnv)

> bindClassEntities :: ModuleIdent -> TCEnv -> TypeInfo -> ValueEnv -> ValueEnv
> bindClassEntities m tcEnv (TypeClass cls _ _ fs) tyEnv = foldr ($) tyEnv $
>   bindClassDict m (qDictConstrId cls) (arrowArity ty) (polyType ty) :
>   zipWith (bindClassFun m)
>           (qDefaultMethodIds cls)
>           (map (classMethodType tyEnv cls) fs)
>   where ty = classDictType tcEnv tyEnv cls fs
> bindClassEntities _ _ _ tyEnv = tyEnv

> bindClassDict :: ModuleIdent -> QualIdent -> Int -> TypeScheme -> ValueEnv
>               -> ValueEnv
> bindClassDict m c n ty = bindEntity m c (DataConstructor c n stdConstrInfo ty)

> bindClassFun :: ModuleIdent -> QualIdent -> TypeScheme -> ValueEnv -> ValueEnv
> bindClassFun m f ty = bindEntity m f (Value f 0 ty)

> classDecls :: TCEnv -> ValueEnv -> Position -> Ident -> Ident -> [Decl Type]
>            -> [TopDecl Type]
> classDecls tcEnv tyEnv p cls tv ds =
>   dictDataDecl p cls tv [dictConstrDecl tcEnv p cls tv tys'] :
>   zipWith4 functDecl
>            ps
>            (defaultMethodIds cls)
>            (repeat [])
>            (zipWith (defaultMethodExpr tyEnv) fs vds')
>   where (vds,ods) = partition isValueDecl ds
>         (ps,fs,tys) = unzip3 [(p,f,ty) | TypeSig p fs ty <- ods, f <- fs]
>         tys' = map (expandMethodType tcEnv (qualify cls) tv) tys
>         vds' = orderMethodDecls (map Just fs) vds

> classIDecls :: ModuleIdent -> TCEnv -> Position -> QualIdent -> Maybe KindExpr
>             -> Ident -> Maybe [Maybe IMethodDecl] -> [IDecl]
> classIDecls m tcEnv p cls k tv (Just ds) =
>   dictIDataDecl IDataDecl p cls k tv
>                 [Just (dictConstrDecl tcEnv p (unqualify cls) tv tys')] :
>   zipWith3 (intfMethodDecl cls tv)
>            (map (maybe p pos) ds)
>            (qDefaultMethodIds cls)
>            tys
>   where tys = map (maybe (QualTypeExpr [] (VariableType tv)) methodType) ds
>         tys' = map (toMethodType m cls tv) tys
>         pos (IMethodDecl p _ _) = p
>         methodType (IMethodDecl _ _ ty) = ty
> classIDecls _ _ p cls k tv Nothing =
>   [dictIDataDecl (const . HidingDataDecl) p cls k tv]

> classDictType :: TCEnv -> ValueEnv -> QualIdent -> [Maybe Ident] -> Type
> classDictType tcEnv tyEnv cls =
>   foldr (TypeArrow . transformType tcEnv . classMethodType tyEnv cls) ty
>   where ty = dictType (TypePred cls (TypeVariable 0))
>         transformType tcEnv (ForAll _ ty) = transformMethodType tcEnv ty

> classMethodType :: ValueEnv -> QualIdent -> Maybe Ident -> TypeScheme
> classMethodType tyEnv cls (Just f) = funType (qualifyLike cls f) tyEnv
> classMethodType _ cls Nothing = ForAll 1 (QualType [TypePred cls ty] ty)
>   where ty = TypeVariable 0

> dictDataDecl :: Position -> Ident -> Ident -> [ConstrDecl] -> TopDecl a
> dictDataDecl p cls tv cs = DataDecl p [] (dictTypeId cls) [tv] cs []

> dictIDataDecl :: (Position -> [ClassAssert] -> QualIdent -> Maybe KindExpr
>                   -> [Ident] -> a)
>               -> Position -> QualIdent -> Maybe KindExpr -> Ident -> a
> dictIDataDecl f p cls k tv =
>   f p [] (qDictTypeId cls) (fmap (`ArrowKind` Star) k) [tv]

> dictConstrDecl :: TCEnv -> Position -> Ident -> Ident -> [QualType]
>                -> ConstrDecl
> dictConstrDecl tcEnv p cls tv tys =
>   ConstrDecl p (filter (tv /=) (nub (fv tys'))) [] (dictConstrId cls) tys'
>   where tvs = tv : filter (unRenameIdent tv /=) nameSupply
>         tys' = map (fromType tcEnv tvs . transformMethodType tcEnv) tys

> defaultMethodExpr :: ValueEnv -> Ident -> Maybe (Decl Type) -> Expression Type
> defaultMethodExpr tyEnv _ (Just (FunctionDecl p f eqs)) =
>   Let [FunctionDecl p f eqs] (mkVar (rawType (varType f tyEnv)) f)
> defaultMethodExpr tyEnv f Nothing = prelUndefined (rawType (varType f tyEnv))

> transformMethodType :: TCEnv -> QualType -> Type
> transformMethodType tcEnv =
>   transformType . contextMap (maxContext tcEnv . tail)

> defaultMethodIds :: Ident -> [Ident]
> defaultMethodIds cls = map (defaultMethodId cls) [1..]
>   where defaultMethodId cls n =
>           mkIdent ("_Method#" ++ name cls ++ "#" ++ show n)

> qDefaultMethodIds :: QualIdent -> [QualIdent]
> qDefaultMethodIds cls =
>   map (qualifyLike cls) (defaultMethodIds (unqualify cls))

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
is defined. Recall that the compiler uses expanded contexts for the
dictionary transformation and therefore the stub function has three
arguments rather than one. This is necessary because the compiler may
not always be able to distinguish class methods from overloaded
functions.

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

> methodStubs :: ModuleIdent -> TCEnv -> ValueEnv -> TopDecl a
>             -> DictState [TopDecl Type]
> methodStubs m tcEnv tyEnv (ClassDecl _ _ cls tv ds) =
>   do
>     us <- mapM (freshVar m "_#dict" . dictType) cx
>     uss <- mapM (mapM (freshVar m "_#dict")) tyss
>     vs <- mapM (freshVar m "_#method") tys
>     let t = dictPattern ty cls' vs
>         ts = map (uncurry VariablePattern) us
>         tss = map ((ts ++) . map (uncurry VariablePattern)) uss
>         es = zipWith3 (methodStubExpr (us!!i) t) ps vs uss
>     return (zipWith4 functDecl ps fs tss es)
>   where (tys,ty) = arrowUnapply (classDictType tcEnv tyEnv cls' (map Just fs))
>         tyss = zipWith (methodDictTypes tyEnv) fs tys
>         cls' = qualifyWith m cls
>         (i,cx) = methodStubContext tcEnv cls'
>         (ps,fs) = unzip [(p,f) | TypeSig p fs _ <- ds, f <- fs]
> methodStubs _ _ _ _ = return []

> intfMethodStubs :: QualIdent -> Ident -> [Maybe IMethodDecl] -> [IDecl]
> intfMethodStubs cls tv ds = map (intfMethodStub cls tv) (catMaybes ds)

> intfMethodStub :: QualIdent -> Ident -> IMethodDecl -> IDecl
> intfMethodStub cls tv (IMethodDecl p f ty) =
>   intfMethodDecl cls tv p (qualifyLike cls f) ty

> intfMethodDecl :: QualIdent -> Ident -> Position -> QualIdent -> QualTypeExpr
>                -> IDecl
> intfMethodDecl cls tv p f (QualTypeExpr cx ty) =
>   IFunctionDecl p f Nothing (QualTypeExpr (methodContext cls tv cx) ty)
>   where methodContext cls tv cx = ClassAssert cls (VariableType tv) : cx

> methodStubContext :: TCEnv -> QualIdent -> (Int,Context)
> methodStubContext tcEnv cls = (i,cx)
>   where tp = TypePred cls (TypeVariable 0)
>         cx = maxContext tcEnv [tp]
>         i = fromJust (elemIndex tp cx)

> methodDictTypes :: ValueEnv -> Ident -> Type -> [Type]
> methodDictTypes tyEnv f ty =
>   take (length tys - arrowArity (rawType (varType f tyEnv))) tys
>   where tys = arrowArgs ty

> dictPattern :: Type -> QualIdent -> [(Type,Ident)] -> ConstrTerm Type
> dictPattern ty cls vs =
>   ConstructorPattern ty (qDictConstrId cls) (map (uncurry VariablePattern) vs)

> methodStubExpr :: (Type,Ident) -> ConstrTerm Type -> Position -> (Type,Ident)
>                -> [(Type,Ident)] -> Expression Type
> methodStubExpr u t p v us =
>   Case (uncurry mkVar u)
>        [caseAlt p t (apply (uncurry mkVar v) (map (uncurry mkVar) us))]

\end{verbatim}
\paragraph{Instance Declarations}
For every instance declaration
\begin{displaymath}
  \mbox{\texttt{instance} \texttt{(}$C_1\,u_{i_1}$\texttt{,}
    \dots\texttt{,} $C_l\,u_{i_o}$\texttt{)} \texttt{=>}
    $C$ \texttt{($T\,u_1\dots\,u_l$)} \texttt{where} \texttt{\lb}
    $h_{i_1}$ \texttt{=} $e_{i_1}$\texttt{;} \dots\texttt{;}
    $h_{i_m}$ \texttt{=} $e_{i_m}$ \texttt{\rb}},
\end{displaymath}
where the instance methods $h_{i_1}, \dots, h_{i_m}$ are
a subset of the methods $f_1, \dots, f_n$ declared for class $C$, a
global function
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

> bindInstFuns :: ModuleIdent -> TCEnv -> (CT,(ModuleIdent,Context))
>              -> ValueEnv -> ValueEnv
> bindInstFuns m tcEnv (CT cls tc,(m',cx)) tyEnv = foldr ($) tyEnv $
>   zipWith (bindInstFun m)
>           (qInstFunId m' tp : qInstMethodIds m' tp)
>           (qualDictType cx' tp : map (instMethodType tyEnv cx tp) fs)
>   where tp = TypePred cls (applyType (TypeConstructor tc) tvs)
>         n = kindArity (constrKind tc tcEnv) - kindArity (classKind cls tcEnv)
>         tvs = take n (map TypeVariable [0..])
>         cx' = maxContext tcEnv cx
>         fs = classMethods cls tcEnv

> bindInstFun :: ModuleIdent -> QualIdent -> QualType -> ValueEnv -> ValueEnv
> bindInstFun m f ty = bindEntity m f (Value f 0 (typeScheme ty))

> instDecls :: ModuleIdent -> TCEnv -> ValueEnv -> Position -> QualIdent
>           -> QualType -> [Decl Type] -> [TopDecl Type] 
> instDecls m tcEnv tyEnv p cls (QualType cx ty) ds =
>   zipWith4 functDecl
>            (p : map (maybe p pos) ds')
>            (instFunId tp : instMethodIds tp)
>            (repeat [])
>            (dictExpr ty' cls (zipWith const (qInstMethodIds m tp) ds') :
>             zipWith3 instMethodExpr (qDefaultMethodIds cls) tys' ds')
>   where tp = TypePred cls ty
>         fs = classMethods cls tcEnv
>         ty' = instDictType tcEnv tyEnv tp fs
>         tys' = [ty | QualType _ ty <- map (instMethodType tyEnv cx tp) fs]
>         ds' = orderMethodDecls fs ds
>         pos (FunctionDecl p _ _) = p

> instMethodExpr :: QualIdent -> Type -> Maybe (Decl Type) -> Expression Type
> instMethodExpr _ ty (Just (FunctionDecl p f eqs)) =
>   Let [FunctionDecl p f eqs] (mkVar ty f)
> instMethodExpr f ty Nothing = Variable ty f

> instIDecls :: TCEnv -> ValueEnv -> Position -> QualIdent -> QualType
>            -> ModuleIdent -> [IDecl]
> instIDecls tcEnv tyEnv p cls (QualType cx ty) m =
>   -- FIXME: omit declarations for hidden methods since they cannot
>   --        be used (and their type is almost always wrong)
>   zipWith (instIDecl tcEnv nameSupply p)
>           (qInstFunId m tp : qInstMethodIds m tp)
>           (qualDictType cx' tp : map (instMethodType tyEnv cx tp) fs)
>   where tp = TypePred cls ty
>         cx' = maxContext tcEnv cx
>         fs = classMethods cls tcEnv

> instIDecl :: TCEnv -> [Ident] -> Position -> QualIdent -> QualType -> IDecl
> instIDecl tcEnv tvs p f ty =
>   IFunctionDecl p f Nothing (fromQualType tcEnv tvs ty)

> instDictType :: TCEnv -> ValueEnv -> TypePred -> [Maybe Ident] -> Type
> instDictType tcEnv tyEnv (TypePred cls ty) fs =
>   instanceType ty (classDictType tcEnv tyEnv cls fs)

> instMethodType :: ValueEnv -> Context -> TypePred -> Maybe Ident -> QualType
> instMethodType tyEnv cx (TypePred cls ty) f =
>   contextMap (cx ++) (instanceType ty (contextMap tail ty'))
>   where ForAll _ ty' = classMethodType tyEnv cls f

> dictExpr :: Type -> QualIdent -> [QualIdent] -> Expression Type
> dictExpr ty cls fs =
>   apply (Constructor ty (qDictConstrId cls))
>         (zipWith Variable (arrowArgs ty) fs)

> orderMethodDecls :: [Maybe Ident] -> [Decl a] -> [Maybe (Decl a)]
> orderMethodDecls fs ds =
>   map (>>= flip lookup [(unRenameIdent f,d) | d@(FunctionDecl _ f _) <- ds])
>       fs

> instMethodIds :: TypePred -> [Ident]
> instMethodIds (TypePred cls ty) =
>   map (instMethodId cls (rootOfType ty)) [1..]
>   where instMethodId cls tc n =
>           mkIdent ("_Method#" ++ qualName cls ++ "#"
>                               ++ qualName tc ++ "#" ++ show n)

> qInstMethodIds :: ModuleIdent -> TypePred -> [QualIdent]
> qInstMethodIds m = map (qualifyWith m) . instMethodIds

\end{verbatim}
\paragraph{Adding Dictionary Arguments}
Given a function $f$ with type $(C_1\,u_1, \dots, C_n\,u_n)
\Rightarrow \tau$, the compiler adds $n$ implicit dictionary arguments
to the function's declaration thereby changing $f$'s type into
$T_1\,u_1 \rightarrow \dots \rightarrow T_n\,u_n \rightarrow \tau$,
where $T_i=\emph{dictTypeId}(C_i)$. The types of these variables are
recorded in the type environment and an environment mapping the
constraints $C_i\,u_i$ onto their corresponding dictionary arguments
is computed as well. This environment is used when transforming
function applications in $f$'s body.

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

> type DictEnv = Env TypePred (Expression Type)

> dictTransValues :: TCEnv -> ValueEnv -> ValueEnv
> dictTransValues tcEnv = fmap transInfo
>   where transInfo (DataConstructor c _ ci (ForAll n ty)) =
>           DataConstructor c (arrowArity ty') (constrInfo ci)
>                           (ForAll n (qualType ty'))
>           where ty' = transformConstrType tcEnv ci ty
>                 constrInfo (ConstrInfo n _) = ConstrInfo n []
>         transInfo (NewtypeConstructor c ty) =
>           NewtypeConstructor c (tmap (qualType . unqualType) ty)
>         transInfo (Value f n ty) = Value f n' ty'
>           where n' = n + arrowArity (rawType ty') - arrowArity (rawType ty)
>                 ty' = tmap (qualType . transformQualType tcEnv) ty

> class DictTrans a where
>   dictTrans :: ModuleIdent -> TCEnv -> NewtypeEnv -> InstEnv -> ValueEnv
>             -> DictEnv -> a Type -> DictState (a Type)

> instance DictTrans TopDecl where
>   dictTrans m tcEnv nEnv iEnv tyEnv dictEnv (DataDecl p cxL tc tvs cs clss) =
>     return (DataDecl p [] tc tvs (map dictTransConstrDecl cs) clss)
>     where dictTransConstrDecl (ConstrDecl p evs cxR c tys) =
>             dictTransConstrDecl' p evs cxR c tys
>           dictTransConstrDecl (ConOpDecl p evs cxR ty1 op ty2) =
>             dictTransConstrDecl' p evs cxR op [ty1,ty2]
>           dictTransConstrDecl' p evs cxR c tys = ConstrDecl p evs [] c tys'
>             where tys' = map (fromType tcEnv (tvs ++ evs)) . arrowArgs $
>                          uncurry (transformConstrType tcEnv) $
>                          expandConstrType tcEnv cxL (qualify tc) tvs cxR tys
>   dictTrans _ _ _ _ _ _ (NewtypeDecl p cx tc tvs nc clss) =
>     return (NewtypeDecl p [] tc tvs nc clss)
>   dictTrans m tcEnv nEnv iEnv tyEnv dictEnv (BlockDecl d) =
>     liftM BlockDecl (dictTrans m tcEnv nEnv iEnv tyEnv dictEnv d)
>   dictTrans _ _ _ _ _ _ d = return d

> instance DictTrans Decl where
>   dictTrans m tcEnv nEnv iEnv tyEnv dictEnv (FunctionDecl p f eqs) =
>     liftM (FunctionDecl p f)
>           (mapM (dictTrans m tcEnv nEnv iEnv tyEnv dictEnv) eqs)
>   dictTrans m tcEnv nEnv iEnv tyEnv dictEnv (PatternDecl p t rhs) =
>     case t of
>       VariablePattern _ v
>         | not (null (context (varType v tyEnv))) ->
>             dictTrans m tcEnv nEnv iEnv tyEnv dictEnv (funDecl p v rhs)
>         where context (ForAll _ (QualType cx _)) = cx
>               funDecl p v rhs =
>                 FunctionDecl p v [Equation p (FunLhs v []) rhs]
>       _ ->
>         do
>           (dictEnv',t') <- dictTransTerm m tcEnv nEnv tyEnv dictEnv t
>           rhs' <- dictTrans m tcEnv nEnv iEnv tyEnv dictEnv' rhs
>           return (PatternDecl p t' rhs')
>   dictTrans _ _ _ _ _ _ d = return d

> instance DictTrans Equation where
>   dictTrans m tcEnv nEnv iEnv tyEnv dictEnv (Equation p (FunLhs f ts) rhs) =
>     do
>       (dictEnv',ts') <- addDictArgs m tcEnv nEnv tyEnv dictEnv cx ts
>       rhs' <- dictTrans m tcEnv nEnv iEnv tyEnv dictEnv' rhs
>       return (Equation p (FunLhs f ts') rhs')
>     where cx = matchContext tcEnv nEnv (varType f tyEnv) $
>                foldr (TypeArrow . typeOf) (typeOf rhs) ts

> instance DictTrans Rhs where
>   dictTrans m tcEnv nEnv iEnv tyEnv dictEnv (SimpleRhs p e ds) =
>     liftM2 (SimpleRhs p)
>            (dictTrans m tcEnv nEnv iEnv tyEnv dictEnv e)
>            (mapM (dictTrans m tcEnv nEnv iEnv tyEnv dictEnv) ds)

> addDictArgs :: ModuleIdent -> TCEnv -> NewtypeEnv -> ValueEnv -> DictEnv
>             -> Context -> [ConstrTerm Type]
>             -> DictState (DictEnv,[ConstrTerm Type])
> addDictArgs m tcEnv nEnv tyEnv dictEnv cx ts =
>   do
>     xs <- mapM (freshVar m "_#dict" . dictType) cx
>     let dictEnv' = foldr bindDict dictEnv (zip cx xs)
>     (dictEnv'',ts') <-
>       mapAccumM (dictTransTerm m tcEnv nEnv tyEnv) dictEnv' ts
>     return (dictEnv'',map (uncurry VariablePattern) xs ++ ts')
>   where bindDict (tp,x) = bindEnv tp (uncurry mkVar x)

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
>   dictTrans _ _ _ _ _ _ (Literal ty l) = return (Literal ty l)
>   dictTrans m tcEnv nEnv iEnv tyEnv dictEnv (Variable ty v) =
>     return (apply (Variable (foldr (TypeArrow . typeOf) ty xs) v) xs)
>     where xs = map (dictArg tcEnv iEnv dictEnv) cx
>           cx = matchContext tcEnv nEnv (funType v tyEnv) ty
>   dictTrans m tcEnv nEnv iEnv tyEnv dictEnv (Constructor ty c) =
>     return (apply (Constructor (foldr (TypeArrow . typeOf) ty xs) c) xs)
>     where xs = map (dictArg tcEnv iEnv dictEnv) cx
>           cx = matchContext tcEnv nEnv (conTypeRhs c tyEnv) ty
>   dictTrans m tcEnv nEnv iEnv tyEnv dictEnv (Apply e1 e2) =
>     liftM2 Apply
>            (dictTrans m tcEnv nEnv iEnv tyEnv dictEnv e1)
>            (dictTrans m tcEnv nEnv iEnv tyEnv dictEnv e2)
>   dictTrans m tcEnv nEnv iEnv tyEnv dictEnv (Let ds e) =
>     liftM2 Let
>            (mapM (dictTrans m tcEnv nEnv iEnv tyEnv dictEnv) ds)
>            (dictTrans m tcEnv nEnv iEnv tyEnv dictEnv e)
>   dictTrans m tcEnv nEnv iEnv tyEnv dictEnv (Case e as) =
>     liftM2 Case
>            (dictTrans m tcEnv nEnv iEnv tyEnv dictEnv e)
>            (mapM (dictTrans m tcEnv nEnv iEnv tyEnv dictEnv) as)

> instance DictTrans Alt where
>   dictTrans m tcEnv nEnv iEnv tyEnv dictEnv (Alt p t rhs) =
>     do
>       (dictEnv',t') <- dictTransTerm m tcEnv nEnv tyEnv dictEnv t
>       rhs' <- dictTrans m tcEnv nEnv iEnv tyEnv dictEnv' rhs
>       return (Alt p t' rhs')

> dictTransTerm :: ModuleIdent -> TCEnv -> NewtypeEnv -> ValueEnv -> DictEnv
>               -> ConstrTerm Type -> DictState (DictEnv,ConstrTerm Type)
> dictTransTerm _ _ _ _ dictEnv (LiteralPattern ty l) =
>   return (dictEnv,LiteralPattern ty l)
> dictTransTerm _ _ _ _ dictEnv (VariablePattern ty v) =
>   return (dictEnv,VariablePattern ty v)
> dictTransTerm m tcEnv nEnv tyEnv dictEnv (ConstructorPattern ty c ts) =
>   do
>     (dictEnv',ts') <- addDictArgs m tcEnv nEnv tyEnv dictEnv cx ts 
>     return (dictEnv',ConstructorPattern ty c ts')
>   where cx = matchContext tcEnv nEnv (conTypeRhs c tyEnv) $
>              foldr (TypeArrow . typeOf) ty ts
> dictTransTerm m tcEnv nEnv tyEnv dictEnv (AsPattern v t) =
>   do
>     (dictEnv',t') <- dictTransTerm m tcEnv nEnv tyEnv dictEnv t
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

> dictArg :: TCEnv -> InstEnv -> DictEnv -> TypePred -> Expression Type
> dictArg tcEnv iEnv dictEnv tp =
>   fromMaybe (instDict tcEnv iEnv dictEnv tp) (lookupEnv tp dictEnv)

> instDict :: TCEnv -> InstEnv -> DictEnv -> TypePred -> Expression Type
> instDict tcEnv iEnv dictEnv tp =
>   instFunApp tcEnv iEnv dictEnv (instContext tcEnv iEnv tp) tp

> instFunApp :: TCEnv -> InstEnv -> DictEnv -> (ModuleIdent,Context) -> TypePred
>            -> Expression Type
> instFunApp tcEnv iEnv dictEnv (m,cx) tp =
>   apply (Variable (transformType (qualDictType cx tp)) (qInstFunId m tp))
>         (map (dictArg tcEnv iEnv dictEnv) cx)

> instContext :: TCEnv -> InstEnv -> TypePred -> (ModuleIdent,Context)
> instContext tcEnv iEnv (TypePred cls ty) =
>   case unapplyType True ty of
>     (TypeConstructor tc,tys) ->
>       case lookupEnv (CT cls tc) iEnv of
>         Just (m,cx) -> (m,map (expandAliasType tys) (maxContext tcEnv cx))
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
method $f$ from class $C$ by an application $f\,d_1 \dots d_n$, where
$d_1,\dots,d_n$ are expressions returning suitable dictionaries for
the instances of $C$ and all of its super classes at the type where
the method is used (cf.~the code of \texttt{methodStubs} above). Since
only single parameter classes are allowed, all dictionary expressions
$d_i$ must have a type of the form $D_i\,\tau$, where $D_i$ is the
dictionary type constructor corresponding to $C$ or one of its super
classes and $\tau$ is the type of the instance at which the method is
used.

In order to replace method calls efficiently, we collect all known
type class methods in an environment that maps each method $f$ onto a
triple consisting of the position of the method's class $C$ in the
(sorted) list of all of its super classes, the number of super
classes, and a function that computes the name of the instance method
for $f$ at a particular type.
\label{dict-specialize}
\begin{verbatim}

> type MethodEnv = Env QualIdent (Int,Int,Type -> Ident)

> dictSpecializeModule :: TCEnv -> Module Type -> Module Type
> dictSpecializeModule tcEnv (Module m es is ds) =
>   Module m es is (map (dictSpecialize (methodEnv tcEnv)) ds)

> methodEnv :: TCEnv -> MethodEnv
> methodEnv tcEnv = foldr bindMethods emptyEnv (allEntities tcEnv)
>   where bindMethods (DataType _ _ _) mEnv = mEnv
>         bindMethods (RenamingType _ _ _) mEnv = mEnv
>         bindMethods (AliasType _ _ _ _) mEnv = mEnv
>         bindMethods (TypeClass cls _ _ fs) mEnv =
>           foldr ($) mEnv (zipWith (bindMethod cls i (length cx)) fs [0..])
>           where (i,cx) = methodStubContext tcEnv cls
>         bindMethods (TypeVar _) mEnv = mEnv
>         bindMethod cls i n (Just f) j =
>           bindEnv (qualifyLike cls f) (i,n,instMethodId cls j)
>         bindMethod _ _ _ Nothing _ = id
>         instMethodId cls j ty = instMethodIds (TypePred cls ty) !! j

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
>   dictSpecialize mEnv (FunctionDecl p f eqs) =
>     FunctionDecl p f (map (dictSpecialize mEnv) eqs)
>   dictSpecialize _ (ForeignDecl p cc s ie f ty) = ForeignDecl p cc s ie f ty
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
$\tau$, we must be careful to apply the instance method to all
dictionaries required by the instance's context. These dictionaries
can be determined by looking at the argument expression for the
$C\,\tau$ instance dictionary to which the method stub $f$ is applied.
This expression is either an application of the global $C\,\tau$
instance creation function to exactly the dictionaries required by the
instance's context or it is a variable that was introduced for an
implicit dictionary argument of a data constructor in a pattern of an
enclosing expression. In the former case, we can simply copy the
dictionary arguments of the instance creation function to the
specialized application of $f'$. In the latter case we cannot
specialize the method application. Fortunately, this will happen only
when the data constructor's declaration includes right hand side
constraints for a universally quantified type variable \emph{and} the
constructor is used at a fixed type for one of these variables, e.g.,
\begin{verbatim}
  data Bag a = Ord a => Bag [a]
  insertInt :: Int -> Bag Int -> Bag Int
  insertInt x (Bag xs) = Bag (ys ++ x:zs) where (ys,zs) = span (< x) xs
\end{verbatim}
In this rather contrived example, the compiler cannot use the
\texttt{Int} implementation of \texttt{Ord}'s \texttt{(<)} method but
will rather use the type class' method stub.

Note that $C$'s dictionary is not necessarily the first argument of
the instance creation function. This is the reason why the position of
$C$ in the list of its super classes is recorded in the method
environment.
\begin{verbatim}

> dictSpecializeApp :: MethodEnv -> Expression Type -> [Expression Type]
>                   -> Expression Type
> dictSpecializeApp _ (Literal ty l) es = apply (Literal ty l) es
> dictSpecializeApp mEnv (Variable ty v) es =
>   case lookupEnv v mEnv of
>     Just (i,n,instMethodId)
>       | isKnownType ty' && isQualified f' ->
>           apply (Variable ty'' f'') (es'' ++ es')
>       | otherwise -> apply (Variable ty v) es
>       where f = apply (Variable ty v) ds
>             (ds,es') = splitAt n es
>             (Variable _ f',es'') = unapply (ds !! i) []
>             TypeApply (TypeConstructor _) ty' = typeOf (head ds)
>             f'' = qualifyLike f' (instMethodId ty')
>             ty'' = foldr (TypeArrow . typeOf) (typeOf f) es''
>     Nothing -> apply (Variable ty v) es
> dictSpecializeApp _ (Constructor ty c) es = apply (Constructor ty c) es
> dictSpecializeApp mEnv (Apply e1 e2) es =
>   dictSpecializeApp mEnv e1 (dictSpecialize mEnv e2 : es)
> dictSpecializeApp mEnv (Let ds e) es =
>   apply (Let (map (dictSpecialize mEnv) ds) (dictSpecialize mEnv e)) es
> dictSpecializeApp mEnv (Case e as) es =
>   apply (Case (dictSpecialize mEnv e) (map (dictSpecialize mEnv) as)) es

> isKnownType :: Type -> Bool
> isKnownType (TypeConstructor _) = True
> isKnownType (TypeVariable _) = False
> isKnownType (TypeConstrained _ _) = True
> isKnownType (TypeSkolem _) = False
> isKnownType (TypeApply ty _) = isKnownType ty
> isKnownType (TypeArrow _ _) = True

> unapply :: Expression a -> [Expression a] -> (Expression a,[Expression a])
> unapply (Literal ty l) es = (Literal ty l,es)
> unapply (Variable ty x) es = (Variable ty x,es)
> unapply (Constructor ty c) es = (Constructor ty c,es)
> unapply (Apply e1 e2) es = unapply e1 (e2:es)
> unapply (Let ds e) es = (Let ds e,es)
> unapply (Case e as) es = (Case e as,es)

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

Another problem is that newtype constructors have been removed from
the source at this point. Thus, newtypes are effectively like type
synonyms and eventually must be expanded in order to match types
successfully. However, one must be careful with expanding newtypes
because they may be recursive. For that reason, \texttt{match} expands
newtypes lazily.
\begin{verbatim}

> newExpand :: NewtypeEnv -> Type -> [Type]
> newExpand nEnv ty = ty : expand nEnv (unapplyType True ty)
>   where expand nEnv (TypeConstructor tc,tys) =
>           case lookupEnv tc nEnv of
>             Just ty -> newExpand (unbindEnv tc nEnv) (expandAliasType tys ty)
>             Nothing -> []
>         expand _ _ = []

> matchContext :: TCEnv -> NewtypeEnv -> TypeScheme -> Type -> Context
> matchContext tcEnv nEnv (ForAll _ (QualType cx ty1)) ty2 =
>   foldr (\(cx1,cx2) cx' -> fromMaybe cx' (qualMatch nEnv cx1 ty1 cx2 ty2))
>         (error "impossible: matchContext")
>         (splits (maxContext tcEnv cx))

> qualMatch :: NewtypeEnv -> Context -> Type -> Context -> Type -> Maybe Context
> qualMatch nEnv cx1 ty1 cx2 ty2 =
>   case contextMatch cx2 ty2 of
>     Just ty2' ->
>       case match nEnv ty1 ty2' idSubst of
>         Just sigma -> Just (subst sigma cx1)
>         Nothing ->
>           internalError ("qualMatch (" ++ show ty1 ++ ") (" ++ show ty2 ++ ")")
>     Nothing -> Nothing

> contextMatch :: Context -> Type -> Maybe Type
> contextMatch [] ty = Just ty
> contextMatch (tp:cx) ty =
>   case ty of
>     TypeArrow ty1 ty2 | ty1 == dictType tp -> contextMatch cx ty2
>     _ -> Nothing

> match :: NewtypeEnv -> Type -> Type -> TypeSubst -> Maybe TypeSubst
> match nEnv ty1 ty2 sigma = listToMaybe $ catMaybes $
>   [match1 nEnv ty1 ty2 sigma | ty1 <- tys1, ty2 <- tys2]
>   where tys1 = newExpand nEnv ty1
>         tys2 = newExpand nEnv ty2

> match1 :: NewtypeEnv -> Type -> Type -> TypeSubst -> Maybe TypeSubst
> match1 _ (TypeConstructor tc1) (TypeConstructor tc2) sigma
>   | tc1 == tc2 = Just sigma
> match1 _ (TypeVariable tv) ty sigma
>   | tv >= 0 = Just (bindSubst tv ty sigma)
> match1 _ (TypeVariable tv1) (TypeVariable tv2) sigma
>   | tv1 == tv2 = Just sigma
> match1 _ (TypeConstrained _ tv1) (TypeConstrained _ tv2) sigma
>   | tv1 == tv2 = Just sigma
> match1 _ (TypeSkolem k1) (TypeSkolem k2) sigma
>   | k1 == k2 = Just sigma
> match1 nEnv (TypeApply ty11 ty12) (TypeApply ty21 ty22) sigma =
>   match nEnv ty11 ty21 sigma >>= match nEnv ty12 ty22
> match1 nEnv (TypeArrow ty11 ty12) (TypeArrow ty21 ty22) sigma =
>   match nEnv ty11 ty21 sigma >>= match nEnv ty12 ty22
> match1 nEnv (TypeApply ty11 ty12) (TypeArrow ty21 ty22) sigma =
>   match nEnv ty11 (TypeApply (TypeConstructor qArrowId) ty21) sigma >>=
>   match nEnv ty12 ty22
> match1 nEnv (TypeArrow ty11 ty12) (TypeApply ty21 ty22) sigma =
>   match nEnv (TypeApply (TypeConstructor qArrowId) ty11) ty21 sigma >>=
>   match nEnv ty12 ty22
> match1 _ ty1 (TypeConstrained (ty2:_) tv2) sigma
>   | ty1 == ty2 = Just (bindSubst tv2 ty1 sigma)
> match1 _ (TypeConstrained (ty1:_) tv1) ty2 sigma
>   | ty1 == ty2 = Just (bindSubst tv1 ty2 sigma)
> match1 _ ty1 ty2 sigma = Nothing

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

> dictTypeId :: Ident -> Ident
> dictTypeId cls = mkIdent ("_Dict#" ++ name cls)

> qDictTypeId :: QualIdent -> QualIdent
> qDictTypeId cls = qualifyLike cls (dictTypeId (unqualify cls))

> dictConstrId :: Ident -> Ident
> dictConstrId = dictTypeId

> qDictConstrId :: QualIdent -> QualIdent
> qDictConstrId = qDictTypeId

\end{verbatim}
The functions \texttt{instFunId} and \texttt{qInstFunId} return the
name of the global function which returns the dictionary for a
particular C-T instance pair.
\begin{verbatim}

> instFunId :: TypePred -> Ident
> instFunId (TypePred cls ty) =
>   mkIdent ("_Inst#" ++ qualName cls ++ "#" ++ qualName (rootOfType ty))

> qInstFunId :: ModuleIdent -> TypePred -> QualIdent
> qInstFunId m = qualifyWith m . instFunId

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
>     updateSt_ (localBindTopEnv x (Value (qualifyWith m x) 0 (monoType ty)))
>     return (ty,x)

\end{verbatim}
The functions \texttt{constrTypeRhs} and \texttt{conTypeRhs} return
the type (scheme) of a data constructor with the context restricted to
only those predicates which appear on the right hand side of its
declaration.
\begin{verbatim}

> constrTypeRhs :: ConstrInfo -> QualType -> QualType
> constrTypeRhs (ConstrInfo _ cxR) (QualType _ ty) = QualType cxR ty

> conTypeRhs :: QualIdent -> ValueEnv -> TypeScheme
> conTypeRhs c tyEnv = uncurry (tmap . constrTypeRhs) (conType c tyEnv)

\end{verbatim}
Convenience functions for constructing parts of the syntax tree.
\begin{verbatim}

> functDecl :: Position -> Ident -> [ConstrTerm a] -> Expression a -> TopDecl a
> functDecl p f ts e = BlockDecl $ funDecl p f ts e

\end{verbatim}
Prelude entities.
\begin{verbatim}

> prelUndefined :: Type -> Expression Type
> prelUndefined a = Variable a (qualifyWith preludeMIdent (mkIdent "undefined"))

\end{verbatim}
