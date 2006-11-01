% -*- LaTeX -*-
% $Id: DictTrans.lhs 1991 2006-11-01 18:15:48Z wlux $
%
% Copyright (c) 2006, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{DictTrans.lhs}
\section{Introducing Dictionaries}
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
> import Monad
> import Set
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
The introduction of dictionaries is divided into four different
tasks:
\begin{enumerate}
\item Introduce a dictionary type for each class defined in the
  current module,
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
>   run (f m tcEnv tyEnv x >>= \x' -> fetchSt >>= \tyEnv' ->
>        return (bindDictTypes tcEnv,tyEnv',x'))
>       (bindDictConstrs m tcEnv $ bindInstFuns tcEnv iEnv $ rebindFuns tyEnv)

> dictTransModule :: TCEnv -> InstEnv -> ValueEnv -> Module Type
>                 -> (TCEnv,ValueEnv,Module Type)
> dictTransModule tcEnv iEnv tyEnv (Module m es is ds) =
>   doTrans transModule tcEnv iEnv tyEnv m ds
>   where transModule m tcEnv tyEnv ds =
>           liftM (Module m es is) (mapM (dictTransTopDecl m tcEnv tyEnv) ds)

> dictTransTopDecl :: ModuleIdent -> TCEnv -> ValueEnv -> TopDecl Type
>                  -> DictState (TopDecl Type)
> dictTransTopDecl _ _ _ (DataDecl p tc tvs cs) = return (DataDecl p tc tvs cs)
> dictTransTopDecl _ _ _ (NewtypeDecl p tc tvs nc) =
>   return (NewtypeDecl p tc tvs nc)
> dictTransTopDecl _ _ _ (TypeDecl p tc tvs ty) = return (TypeDecl p tc tvs ty)
> dictTransTopDecl _ _ _ (ClassDecl p cls tv) = return (dictDecl p cls tv)
> dictTransTopDecl m _ _ (InstanceDecl p cls ty) = return (instDecl m p cls ty)
> dictTransTopDecl m tcEnv tyEnv (BlockDecl d) =
>   liftM BlockDecl (dictTrans m tyEnv emptyEnv d)

> dictTransGoal :: TCEnv -> InstEnv -> ValueEnv -> ModuleIdent -> Goal Type
>               -> (TCEnv,ValueEnv,Goal Type)
> dictTransGoal tcEnv iEnv tyEnv m g = doTrans transGoal tcEnv iEnv tyEnv m g
>   where transGoal m tcEnv tyEnv = dictTrans m tyEnv emptyEnv

\end{verbatim}
Besides the source code definitions, the compiler must also transform
the imported interface modules because their declarations are used to
supply the appropriate environment for the abstract machine code
generator.
\begin{verbatim}

> dictTransInterface :: Interface -> Interface
> dictTransInterface (Interface m is ds) =
>   Interface m is (map (dictTransIntfDecl m) ds)

> dictTransIntfDecl :: ModuleIdent -> IDecl -> IDecl
> dictTransIntfDecl _ (IInfixDecl p fix pr op) = IInfixDecl p fix pr op
> dictTransIntfDecl _ (HidingDataDecl p tc tvs) = HidingDataDecl p tc tvs
> dictTransIntfDecl _ (IDataDecl p tc tvs cs) = IDataDecl p tc tvs cs
> dictTransIntfDecl _ (INewtypeDecl p tc tvs nc) = INewtypeDecl p tc tvs nc
> dictTransIntfDecl _ (ITypeDecl p tc tvs ty) = ITypeDecl p tc tvs ty
> dictTransIntfDecl _ (HidingClassDecl p cls tv) = dictIDecl False p cls tv
> dictTransIntfDecl _ (IClassDecl p cls tv) = dictIDecl True p cls tv
> dictTransIntfDecl m (IInstanceDecl p cls ty) = instIDecl m p cls ty
> dictTransIntfDecl m (IFunctionDecl p f ty) =
>   IFunctionDecl p f (fromQualType m (transformType (toQualType m [] ty)))

\end{verbatim}
\paragraph{Dictionary types}
For every type class declaration \texttt{class} $C$ $a$ a dictionary
type declaration \texttt{data} $T$ $a$ \texttt{=} $C'$, where
$T=\emph{dictTypeId}(C)$ and $C'=\emph{dictConstrId}(C)$, is added to
the source code and the type constructor and value type environments
are updated accordingly. Since type classes and type constructors
share a common name space, we simply use the identity function for
\emph{dictTypeId}.
\begin{verbatim}

> bindDictTypes :: TCEnv -> TCEnv
> bindDictTypes = fmap transInfo
>   where transInfo (TypeClass cls) = dictTypeInfo cls
>         transInfo ti = ti

> bindDictConstrs :: ModuleIdent -> TCEnv -> ValueEnv -> ValueEnv
> bindDictConstrs m tcEnv tyEnv =
>   foldr (bindDictConstr m) tyEnv [cls | TypeClass cls <- allEntities tcEnv]

> bindDictConstr :: ModuleIdent -> QualIdent -> ValueEnv -> ValueEnv
> bindDictConstr m cls = bindEntity m c (DataConstructor c ty)
>   where c = qualifyLike cls (dictConstrId (unqualify cls))
>         ty = ForAll 1 (qualDictType (TypePred cls (TypeVariable 0)))

> dictDecl :: Position -> Ident -> Ident -> TopDecl Type
> dictDecl p cls tv = DataDecl p (dictTypeId cls) [tv] [dictConstrDecl p cls]

> dictIDecl :: Bool -> Position -> QualIdent -> Ident -> IDecl
> dictIDecl False p cls tv = HidingDataDecl p (qDictTypeId cls) [tv]
> dictIDecl True p cls tv =
>   IDataDecl p (qDictTypeId cls) [tv] [Just (dictConstrDecl p (unqualify cls))]

> dictConstrDecl :: Position -> Ident -> ConstrDecl
> dictConstrDecl p cls = ConstrDecl p [] (dictConstrId cls) []

> dictTypeInfo :: QualIdent -> TypeInfo
> dictTypeInfo cls =
>   DataType (qDictTypeId cls) 1 [Just (dictConstrId (unqualify cls))]

\end{verbatim}
\paragraph{Instance dictionaries}
For every instance declaration \texttt{instance} $C$
$(T\,x_1\dots\,x_n)$ a global function $f$ \texttt{=} $C'$, where
$f=\emph{instFunId}(C,T)$ and $C'=\emph{dictConstrId}(C)$, is added to
the source code and its type is recorded in the type environment.
\begin{verbatim}

> bindInstFuns :: TCEnv -> InstEnv -> ValueEnv -> ValueEnv
> bindInstFuns tcEnv iEnv tyEnv =
>   foldr (bindInstFun tcEnv) tyEnv (toListSet iEnv)

> bindInstFun :: TCEnv -> CT -> ValueEnv -> ValueEnv
> bindInstFun tcEnv ct =
>   importTopEnv False m f (Value (qualifyWith m f) (typeScheme ty))
>   where m = instanceMIdent
>         f = instFunId tp
>         ty = qualDictType tp
>         tp = ctTypePred tcEnv ct

> ctTypePred :: TCEnv -> CT -> TypePred
> ctTypePred tcEnv (CT cls tc) =
>   TypePred cls (TypeConstructor tc (take n (map TypeVariable [0..])))
>   where n = constrKind tc tcEnv

> instDecl :: ModuleIdent -> Position -> QualIdent -> TypeExpr -> TopDecl Type
> instDecl m p cls ty = BlockDecl $
>   funDecl p (instFunId tp) [] (Constructor (dictType tp) (qDictConstrId cls))
>   where tp = toTypePred m cls ty

> instIDecl :: ModuleIdent -> Position -> QualIdent -> TypeExpr -> IDecl
> instIDecl m p cls ty =
>   IFunctionDecl p (qInstFunId tp) (fromQualType m (qualDictType tp))
>   where tp = toTypePred m cls ty

> toTypePred :: ModuleIdent -> QualIdent -> TypeExpr -> TypePred
> toTypePred m cls ty = TypePred (qualQualify m cls) (toType m [] ty)

\end{verbatim}
\paragraph{Adding dictionary arguments}
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
>           Value f (ForAll n (transformType ty))
>         transInfo vi = vi

> class DictTrans a where
>   dictTrans :: ModuleIdent -> ValueEnv -> DictEnv -> a Type
>             -> DictState (a Type)

> instance DictTrans Goal where
>   dictTrans m tyEnv dictEnv (Goal p e ds) =
>     liftM2 (Goal p)
>            (dictTrans m tyEnv dictEnv e)
>            (mapM (dictTrans m tyEnv dictEnv) ds)

> instance DictTrans Decl where
>   dictTrans m tyEnv dictEnv (FunctionDecl p f eqs) =
>     liftM (FunctionDecl p f) (mapM (dictTrans m tyEnv dictEnv) eqs)
>   dictTrans m tyEnv dictEnv (PatternDecl p t rhs) =
>     liftM (PatternDecl p t) (dictTrans m tyEnv dictEnv rhs)
>   dictTrans _ _ _ d = return d

> instance DictTrans Equation where
>   dictTrans m tyEnv dictEnv (Equation p lhs rhs) =
>     do
>       -- FIXME: could share dictionary variables between all equations
>       --        of a function => perform transformation in Decl instance
>       xs <- mapM (freshVar m "_#dict" . dictType) cx
>       liftM (Equation p (addArgs (map (uncurry VariablePattern) xs) lhs))
>             (dictTrans m tyEnv (foldr bindDict dictEnv (zip cx xs)) rhs)
>     where (f,ts) = flatLhs lhs
>           ty = foldr TypeArrow (typeOf rhs) (map typeOf ts)
>           cx = matchContext (varType f tyEnv) ty
>           bindDict (tp,x) = bindEnv tp (uncurry mkVar x)

> addArgs :: [ConstrTerm a] -> Lhs a -> Lhs a
> addArgs xs (FunLhs f ts) = FunLhs f (xs ++ ts)
> addArgs xs (OpLhs t1 op t2) = FunLhs op (xs ++ [t1,t2])
> addArgs xs (ApLhs lhs ts) = ApLhs (addArgs xs lhs) ts

> instance DictTrans Rhs where
>   dictTrans m tyEnv dictEnv (SimpleRhs p e ds) =
>     liftM2 (SimpleRhs p)
>            (dictTrans m tyEnv dictEnv e)
>            (mapM (dictTrans m tyEnv dictEnv) ds)
>   dictTrans m tyEnv dictEnv (GuardedRhs es ds) =
>     liftM2 GuardedRhs
>            (mapM (dictTrans m tyEnv dictEnv) es)
>            (mapM (dictTrans m tyEnv dictEnv) ds)

> instance DictTrans CondExpr where
>   dictTrans m tyEnv dictEnv (CondExpr p g e) =
>     liftM2 (CondExpr p)
>            (dictTrans m tyEnv dictEnv g)
>            (dictTrans m tyEnv dictEnv e)

\end{verbatim}
An application of an overloaded function $f$ with type $(C_1\,x_1,
\dots, C_n\,x_n) \Rightarrow \tau$ is changed into an application of
$f$ to the dictionaries for $C_1\,\tau_1, \dots, C_n\,\tau_n$ where
the types $\tau_i$ are given by $\tau_i = \vartheta x_i$ where
$\vartheta$ is the most general unifier between $f$'s type $\tau$ and
the concrete type at which $f$ is used in the application.
\begin{verbatim}

> instance DictTrans Expression where
>   dictTrans _ _ _ (Literal ty l) = return (Literal ty l)
>   dictTrans m tyEnv dictEnv (Variable ty v) =
>     return (apply (Variable ty' v) xs)
>     where ty' = foldr (TypeArrow . typeOf) ty xs
>           xs = map dictArg (matchContext (funType v tyEnv) ty)
>           dictArg tp = maybe (instFun tp) id (lookupEnv tp dictEnv)
>           instFun tp = Variable (dictType tp) (qInstFunId tp)
>   dictTrans _ _ _ (Constructor ty c) = return (Constructor ty c)
>   dictTrans m tyEnv dictEnv (Paren e) =
>     liftM Paren (dictTrans m tyEnv dictEnv e)
>   dictTrans m tyEnv dictEnv (Typed e ty) =
>     liftM (flip Typed ty) (dictTrans m tyEnv dictEnv e)
>   dictTrans m tyEnv dictEnv (Tuple es) =
>     liftM Tuple (mapM (dictTrans m tyEnv dictEnv) es)
>   dictTrans m tyEnv dictEnv (List ty es) =
>     liftM (List ty) (mapM (dictTrans m tyEnv dictEnv) es)
>   dictTrans m tyEnv dictEnv (ListCompr e sts) =
>     liftM2 ListCompr
>            (dictTrans m tyEnv dictEnv e)
>            (mapM (dictTrans m tyEnv dictEnv) sts)
>   dictTrans m tyEnv dictEnv (EnumFrom e) =
>     liftM EnumFrom (dictTrans m tyEnv dictEnv e)
>   dictTrans m tyEnv dictEnv (EnumFromThen e1 e2) =
>     liftM2 EnumFromThen
>            (dictTrans m tyEnv dictEnv e1)
>            (dictTrans m tyEnv dictEnv e2)
>   dictTrans m tyEnv dictEnv (EnumFromTo e1 e2) =
>     liftM2 EnumFromTo
>            (dictTrans m tyEnv dictEnv e1)
>            (dictTrans m tyEnv dictEnv e2)
>   dictTrans m tyEnv dictEnv (EnumFromThenTo e1 e2 e3) =
>     liftM3 EnumFromThenTo
>            (dictTrans m tyEnv dictEnv e1)
>            (dictTrans m tyEnv dictEnv e2)
>            (dictTrans m tyEnv dictEnv e3)
>   dictTrans m tyEnv dictEnv (UnaryMinus op e) =
>     liftM (UnaryMinus op) (dictTrans m tyEnv dictEnv e)
>   dictTrans m tyEnv dictEnv (Apply e1 e2) =
>     liftM2 Apply
>            (dictTrans m tyEnv dictEnv e1)
>            (dictTrans m tyEnv dictEnv e2)
>   dictTrans m tyEnv dictEnv (InfixApply e1 op e2) =
>     dictTrans m tyEnv dictEnv (apply (infixOp op) [e1,e2])
>   dictTrans m tyEnv dictEnv (LeftSection e op) =
>     dictTrans m tyEnv dictEnv (apply (infixOp op) [e])
>   dictTrans m tyEnv dictEnv (RightSection op e) =
>     dictTrans m tyEnv dictEnv (apply (prelFlip ty1 ty2 ty3) [op',e])
>     where TypeArrow ty1 (TypeArrow ty2 ty3) = typeOf op'
>           op' = infixOp op
>   dictTrans m tyEnv dictEnv (Lambda ts e) =
>     liftM (Lambda ts) (dictTrans m tyEnv dictEnv e)
>   dictTrans m tyEnv dictEnv (Let ds e) =
>     liftM2 Let
>            (mapM (dictTrans m tyEnv dictEnv) ds)
>            (dictTrans m tyEnv dictEnv e)
>   dictTrans m tyEnv dictEnv (Do sts e) =
>     liftM2 Do
>            (mapM (dictTrans m tyEnv dictEnv) sts)
>            (dictTrans m tyEnv dictEnv e)
>   dictTrans m tyEnv dictEnv (IfThenElse e1 e2 e3) =
>     liftM3 IfThenElse
>            (dictTrans m tyEnv dictEnv e1)
>            (dictTrans m tyEnv dictEnv e2)
>            (dictTrans m tyEnv dictEnv e3)
>   dictTrans m tyEnv dictEnv (Case e as) =
>     liftM2 Case
>            (dictTrans m tyEnv dictEnv e)
>            (mapM (dictTrans m tyEnv dictEnv) as)

> instance DictTrans Alt where
>   dictTrans m tyEnv dictEnv (Alt p t rhs) =
>     liftM (Alt p t) (dictTrans m tyEnv dictEnv rhs)

> instance DictTrans Statement where
>   dictTrans m tyEnv dictEnv (StmtExpr e) =
>     liftM StmtExpr (dictTrans m tyEnv dictEnv e)
>   dictTrans m tyEnv dictEnv (StmtBind t e) =
>     liftM (StmtBind t) (dictTrans m tyEnv dictEnv e)
>   dictTrans m tyEnv dictEnv (StmtDecl ds) =
>     liftM StmtDecl (mapM (dictTrans m tyEnv dictEnv) ds)

> transformType :: QualType -> QualType
> transformType (QualType cx ty) =
>   QualType [] (foldr (TypeArrow . dictType) ty cx)

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
> match (TypeGuard tv1) (TypeGuard tv2)
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

\end{verbatim}
\paragraph{Auxiliary functions}
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
> qDictTypeId cls = maybe qualify qualifyWith m (dictTypeId cls')
>   where (m,cls') = splitQualIdent cls

> dictConstrId :: Ident -> Ident
> dictConstrId cls = mkIdent ("_Dict#" ++ name cls)

> qDictConstrId :: QualIdent -> QualIdent
> qDictConstrId cls = maybe qualify qualifyWith m (dictConstrId cls')
>   where (m,cls') = splitQualIdent cls

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
>         typeName (TypeArrow _ _) = name arrowId
>         typeName ty = internalError ("instFunId " ++ show ty)

> qInstFunId :: TypePred -> QualIdent
> qInstFunId = qualifyWith instanceMIdent . instFunId

\end{verbatim}
The functions \texttt{dictType} and \texttt{qualDictType} return the
(qualified) type of the dictionary corresponding to a particular C-T
instance.
\begin{verbatim}

> dictType :: TypePred -> Type
> dictType (TypePred cls ty) = TypeConstructor (qDictTypeId cls) [ty]

> qualDictType :: TypePred -> QualType
> qualDictType tp = QualType [] (dictType tp)

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

> funDecl :: Position -> Ident -> [ConstrTerm a] -> Expression a -> Decl a
> funDecl p f ts e =
>   FunctionDecl p f [Equation p (FunLhs f ts) (SimpleRhs p e [])]

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

\end{verbatim}
