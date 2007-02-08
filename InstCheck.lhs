% -*- LaTeX -*-
% $Id: InstCheck.lhs 2092 2007-02-08 21:30:37Z wlux $
%
% Copyright (c) 2006-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{InstCheck.lhs}
\section{Checking Instances}
After kind checking and before type checking, the compiler checks the
contexts of all instance declarations in the current module and
ensures that all necessary super class instances exist. Furthermore,
the compiler infers the contexts of the implicit instance declarations
introduced by deriving clauses in data and newtype declarations. The
instances declared explicitly and automatically derived by the
compiler are added to the instance environment.
\begin{verbatim}

> module InstCheck(instCheck) where
> import Base
> import CurryPP
> import Env
> import Error
> import List
> import Monad
> import Pretty
> import SCC
> import TopEnv
> import TypeSubst
> import TypeTrans

> instCheck :: ModuleIdent -> TCEnv -> InstEnv -> [TopDecl a] -> Error InstEnv
> instCheck m tcEnv iEnv ds =
>   do
>     iEnv'' <- foldM (bindDerivedInstances m tcEnv) iEnv' (sortDeriving m tds)
>     mapE_ (checkInstance tcEnv iEnv'') ids
>     return iEnv''
>   where (tds,ods) = partition isTypeDecl ds
>         ids = filter isInstanceDecl ods
>         iEnv' = foldr (bindInstance tcEnv) iEnv ids

\end{verbatim}
First, the compiler adds all explicit instance declarations to the
instance environment.
\begin{verbatim}

> bindInstance :: TCEnv -> TopDecl a -> InstEnv -> InstEnv
> bindInstance tcEnv (InstanceDecl _ cx cls ty _) =
>   bindEnv (CT cls' (rootOfType ty')) cx'
>   where cls' = origName (head (qualLookupTopEnv cls tcEnv))
>         QualType cx' ty' = expandPolyType tcEnv (QualTypeExpr cx ty)
> bindInstance _ _ = id

\end{verbatim}
In the next step, the compiler infers the contexts of derived instance
declarations. Given a data type declaration
\begin{displaymath}
  \mbox{\texttt{data} \emph{cx} $\Rightarrow$ $T$ $u_1$ $\dots\;u_k$
    \texttt{=} $K_1$ $t_{11}$ $\dots\;t_{1k_1}$
    \texttt{|} \dots \texttt{|}
    $K_n$ $t_{n1}$ $\dots\;t_{nk_n}$
    \texttt{deriving} \texttt{(}$C_1, \dots, C_m$\texttt{)}}
\end{displaymath}
the context of the instance declaration derived for a class $C \in
\left\{ C_1, \dots, C_m \right\}$ must be of the form $(\emph{cx},
\emph{cx}')$ such that $\emph{cx'} \Rightarrow C\,t_{ij}$ holds for
each constituent type $t_{ij}$ of the data type declaration and that
\emph{cx'} is the minimal context for which this property holds
(cf.\ Chap.~10 of~\cite{PeytonJones03:Haskell}). In the case of
(mutually) recursive data types, inference of the appropriate contexts
may require a fixpoint calculation.

After adding all explicit instance declarations to the instance
environment, the compiler sorts the data and newtype declarations with
non-empty deriving clauses into minimal binding groups and infers
contexts for their instance declarations. While inferring instance
contexts, the compiler must carefully respect the super class
hierarchy so that super class instances are added to the instance
environment before instances of their subclasses.
\begin{verbatim}

> bindDerivedInstances :: ModuleIdent -> TCEnv -> InstEnv -> [TopDecl a]
>                      -> Error InstEnv
> bindDerivedInstances m tcEnv iEnv [DataDecl p cx tc tvs cs clss]
>   | null cs = errorAt p noAbstractDerive
>   | any (`notElem` tvs) (fv tys) = errorAt p noExistentialDerive
>   | tc `notElem` foldr (ft m) [] tys =
>       foldM (bindDerived m tcEnv p cx tc tvs tys) iEnv
>             (sortClasses tcEnv clss)
>   where tys = concatMap constrTypes cs
> bindDerivedInstances m tcEnv iEnv
>                      [NewtypeDecl p cx tc tvs (NewConstrDecl _ _ ty) clss]
>   | tc `notElem` ft m ty [] =
>       foldM (bindDerived m tcEnv p cx tc tvs [ty]) iEnv
>             (sortClasses tcEnv clss)
> bindDerivedInstances m tcEnv iEnv ds =
>   foldM (bindInitialContexts m tcEnv) iEnv ds >>=
>   fixpoint (\iEnv' -> updateContexts iEnv' . concat)
>            (\iEnv' -> mapE (inferContexts m tcEnv iEnv') ds)
>   where fixpoint f m x = m x >>= maybe (return x) (fixpoint f m) . f x

> bindDerived :: ModuleIdent -> TCEnv -> Position -> [ClassAssert] -> Ident
>             -> [Ident] -> [TypeExpr] -> InstEnv -> QualIdent -> Error InstEnv
> bindDerived m tcEnv p cx tc tvs tys iEnv cls =
>   liftM (flip (uncurry bindEnv) iEnv)
>         (inferContext m tcEnv iEnv p cx tc tvs tys cls)

> bindInitialContexts :: ModuleIdent -> TCEnv -> InstEnv -> TopDecl a
>                     -> Error InstEnv
> bindInitialContexts m tcEnv iEnv (DataDecl p cx tc tvs cs clss)
>   | null cs = errorAt p noAbstractDerive
>   | any (`notElem` tvs) (fv tys) = errorAt p noExistentialDerive
>   | otherwise =
>       foldM (bindDerived m tcEnv p cx tc tvs []) iEnv (sortClasses tcEnv clss)
>   where tys = concatMap constrTypes cs
> bindInitialContexts m tcEnv iEnv (NewtypeDecl p cx tc tvs _ clss) =
>   foldM (bindDerived m tcEnv p cx tc tvs []) iEnv (sortClasses tcEnv clss)

> inferContexts :: ModuleIdent -> TCEnv -> InstEnv -> TopDecl a
>               -> Error [(CT,Context)]
> inferContexts m tcEnv iEnv (DataDecl p cx tc tvs cs clss) =
>   mapE (inferContext m tcEnv iEnv p cx tc tvs tys) clss
>   where tys = concatMap constrTypes cs
> inferContexts m tcEnv iEnv
>               (NewtypeDecl p cx tc tvs (NewConstrDecl _ c ty) clss) =
>   mapE (inferContext m tcEnv iEnv p cx tc tvs [ty]) clss

> inferContext :: ModuleIdent -> TCEnv -> InstEnv -> Position -> [ClassAssert]
>              -> Ident -> [Ident] -> [TypeExpr] -> QualIdent
>              -> Error (CT,Context)
> inferContext m tcEnv iEnv p cx tc tvs tys cls =
>   do
>     cx''' <- reduceContext p what doc tcEnv iEnv cx''
>     return (CT cls' tc',sort cx''')
>   where what = "derived instance"
>         doc = ppInstance tcEnv (TypePred cls (arrowBase ty'))
>         QualType cx' ty' = expandConstrType tcEnv cx tc' tvs tys
>         tc' = qualifyWith m tc
>         (cls',clss) =
>           case qualLookupTopEnv cls tcEnv of
>             [TypeClass cls' _ clss _] -> (cls',clss)
>             _ -> internalError "inferContext"
>         cx'' = nub (cx' ++ [TypePred cls (arrowBase ty') | cls <- clss] ++
>                     [TypePred cls' ty | ty <- arrowArgs ty'])

> updateContexts :: InstEnv -> [(CT,Context)] -> Maybe InstEnv
> updateContexts iEnv cxs = if or upds then Just iEnv' else Nothing
>   where (iEnv',upds) = mapAccumL updateInstance iEnv cxs
>         updateInstance iEnv (ct,cx) =
>           case lookupEnv ct iEnv of
>             Just cx'
>               | cx == cx' -> (iEnv,False)
>               | otherwise -> (bindEnv ct cx iEnv,True)
>             Nothing -> internalError "updateContext"

> sortClasses :: TCEnv -> [QualIdent] -> [QualIdent]
> sortClasses tcEnv clss =
>   map fst (sortBy compareDepth (map (adjoinDepth tcEnv) clss))
>   where (_,d1) `compareDepth` (_,d2) = d1 `compare` d2
>         adjoinDepth tcEnv cls = (cls,length (allSuperClasses cls tcEnv))

> sortDeriving :: ModuleIdent -> [TopDecl a] -> [[TopDecl a]]
> sortDeriving m ds = scc bound free (filter hasDerivedInstance ds)
>   where bound (DataDecl _ _ tc _ _ _) = [tc]
>         bound (NewtypeDecl _ _ tc _ _ _) = [tc]
>         free (DataDecl _ _ _ _ cs _) =
>           foldr (ft m) [] (concatMap constrTypes cs)
>         free (NewtypeDecl _ _ _ _ (NewConstrDecl _ _ ty) _) = ft m ty []

> hasDerivedInstance :: TopDecl a -> Bool
> hasDerivedInstance (DataDecl _ _ _ _ _ clss) = not (null clss)
> hasDerivedInstance (NewtypeDecl _ _ _ _ _ clss) = not (null clss)
> hasDerivedInstance (TypeDecl _ _ _ _) = False
> hasDerivedInstance (ClassDecl _ _ _ _ _) = False
> hasDerivedInstance (InstanceDecl _ _ _ _ _) = False
> hasDerivedInstance (BlockDecl _) = False

> ft :: ModuleIdent -> TypeExpr -> [Ident] -> [Ident]
> ft m (ConstructorType tc) tcs = maybe id (:) (localIdent m tc) tcs
> ft _ (VariableType _) tcs = tcs
> ft m (TupleType tys) tcs = foldr (ft m) tcs tys
> ft m (ListType ty) tcs = ft m ty tcs
> ft m (ArrowType ty1 ty2) tcs = ft m ty1 $ ft m ty2 $ tcs
> ft m (ApplyType ty1 ty2) tcs = ft m ty1 $ ft m ty2 $ tcs

\end{verbatim}
Finally, the compiler checks the contexts of all explicit instance
declarations detecting missing super class instances. Given an
instance declaration
\begin{displaymath}
  \mbox{\texttt{instance} \emph{cx} $\Rightarrow$
    $C$ $(T$ $u_1$ $\dots\;u_k)$ \texttt{where} \dots}
\end{displaymath}
this ensures that $T$ is an instance of all of $C$'s super classes and
also that the contexts of the corresponding instance declarations are
satisfied by \emph{cx}.
\begin{verbatim}

> checkInstance :: TCEnv -> InstEnv -> TopDecl a -> Error ()
> checkInstance tcEnv iEnv (InstanceDecl p cx cls ty ds) =
>   do
>     cx''' <- reduceContext p what doc tcEnv iEnv cx''
>     mapE_ (errorAt p . noInstance what doc tcEnv)
>           (filter (`notElem` maxContext tcEnv cx') cx''')
>   where what = "instance declaration"
>         doc = ppInstance tcEnv (TypePred cls ty')
>         QualType cx' ty' = expandPolyType tcEnv (QualTypeExpr cx ty)
>         cx'' = [TypePred cls ty' | cls <- superClasses cls tcEnv]
> checkInstance _ _ _ = return ()

\end{verbatim}
The function \texttt{reduceContext} simplifies a context
$(C_1\,\tau_1, \dots, C_n\,\tau_n)$ where the $\tau_i$ are arbitrary
types into a context where all predicates are of the form $C\,u$ with
$u$ being a type variable. An error is reported if the context cannot
be transformed into this form. In addition, all predicates that are
implied by other predicates in the context are removed.
\begin{verbatim}

> reduceContext :: Position -> String -> Doc -> TCEnv -> InstEnv -> Context
>               -> Error Context
> reduceContext p what doc tcEnv iEnv cx =
>   do
>     mapE_ (errorAt p . noInstance what doc tcEnv) cx2
>     return cx1
>   where (cx1,cx2) =
>           partitionContext (minContext tcEnv (reduceTypePreds iEnv cx))

> reduceTypePreds :: InstEnv -> Context -> Context
> reduceTypePreds iEnv = concatMap (reduceTypePred iEnv)

> reduceTypePred :: InstEnv -> TypePred -> Context
> reduceTypePred iEnv (TypePred cls ty) =
>   maybe [TypePred cls ty] (reduceTypePreds iEnv) (instContext iEnv cls ty [])

> instContext :: InstEnv -> QualIdent -> Type -> [Type] -> Maybe Context
> instContext iEnv cls (TypeConstructor tc) tys =
>   fmap (map (expandAliasType tys)) (lookupEnv (CT cls tc) iEnv)
> instContext _ _ (TypeVariable _) _ = Nothing
> instContext _ _ (TypeConstrained _ _) _ = Nothing
> instContext _ _ (TypeSkolem _) _ = Nothing
> instContext iEnv cls (TypeApply ty1 ty2) tys =
>   instContext iEnv cls ty1 (ty2:tys)
> instContext iEnv cls (TypeArrow ty1 ty2) tys =
>   fmap (map (expandAliasType (ty1:ty2:tys)))
>        (lookupEnv (CT cls qArrowId) iEnv)

> partitionContext :: Context -> (Context,Context)
> partitionContext cx = partition (\(TypePred _ ty) -> isTypeVar ty) cx
>   where isTypeVar (TypeConstructor _) = False
>         isTypeVar (TypeVariable _) = True
>         isTypeVar (TypeConstrained _ _) = False
>         isTypeVar (TypeSkolem _) = False
>         isTypeVar (TypeApply _ _) = False
>         isTypeVar (TypeArrow _ _) = False

\end{verbatim}
The function \texttt{constrTypes} extracts the argument types of a
data constructor from its declaration.
\begin{verbatim}

> constrTypes :: ConstrDecl -> [TypeExpr]
> constrTypes (ConstrDecl _ _ _ tys) = tys
> constrTypes (ConOpDecl _ _ ty1 _ ty2) = [ty1,ty2]

\end{verbatim}
Error functions.
\begin{verbatim}

> noInstance :: String -> Doc -> TCEnv -> TypePred -> String
> noInstance what doc tcEnv tp = show $
>   text "Missing" <+> ppInstance tcEnv tp <+> text "instance" $$
>   text "in" <+> text what <+> doc

> noAbstractDerive :: String
> noAbstractDerive = "Instances cannot be derived for abstract types"

> noExistentialDerive :: String
> noExistentialDerive =
>   "Instances cannot be derived for existentially quantified types"

\end{verbatim}
