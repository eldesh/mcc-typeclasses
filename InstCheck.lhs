% -*- LaTeX -*-
% $Id: InstCheck.lhs 2780 2009-03-28 16:25:54Z wlux $
%
% Copyright (c) 2006-2009, Wolfgang Lux
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
compiler are added to the instance environment. Finally, the compiler
also checks that all types specified in a default declaration are
instances of class \texttt{Prelude.Num}.
\begin{verbatim}

> module InstCheck(instCheck) where
> import Base
> import Curry
> import CurryUtils
> import Env
> import Error
> import InstInfo
> import List
> import Monad
> import PredefIdent
> import Pretty
> import SCC
> import TopEnv
> import Types
> import TypeInfo
> import TypeSubst
> import TypeTrans

> instCheck :: ModuleIdent -> TCEnv -> InstEnv -> [TopDecl a] -> Error InstEnv
> instCheck m tcEnv iEnv ds =
>   do
>     mapE_ checkDeriving tds'
>     iEnv'' <-
>       foldM (bindDerivedInstances m tcEnv) iEnv'
>             (sortDeriving (map (declDeriving m tcEnv) tds'))
>     mapE_ (checkInstance tcEnv iEnv'') ids  &&>
>       mapE_ (checkDefault tcEnv iEnv'') dds
>     return iEnv''
>   where (tds,ods) = partition isTypeDecl ds
>         tds' = filter hasDerivedInstance tds
>         ids = filter isInstanceDecl ods
>         dds = filter isDefaultDecl ods
>         iEnv' = foldr (bindInstance m tcEnv) iEnv ids

> hasDerivedInstance :: TopDecl a -> Bool
> hasDerivedInstance (DataDecl _ _ _ _ _ clss) = not (null clss)
> hasDerivedInstance (NewtypeDecl _ _ _ _ _ clss) = not (null clss)
> hasDerivedInstance (TypeDecl _ _ _ _) = False
> hasDerivedInstance (ClassDecl _ _ _ _ _) = False
> hasDerivedInstance (InstanceDecl _ _ _ _ _) = False
> hasDerivedInstance (DefaultDecl _ _) = False
> hasDerivedInstance (BlockDecl _) = False
> hasDerivedInstance (SplitAnnot _) = False

\end{verbatim}
No instances can be derived for abstract data types as well as
existentially quantified data types.
\begin{verbatim}

> checkDeriving :: TopDecl a -> Error ()
> checkDeriving (DataDecl p _ _ _ cs _)
>   | null cs = errorAt p noAbstractDerive
>   | any (not . null . existVars) cs = errorAt p noExistentialDerive
>   where existVars (ConstrDecl _ evs _ _ _) = evs
>         existVars (ConOpDecl _ evs _ _ _ _) = evs
>         existVars (RecordDecl _ evs _ _ _) = evs
> checkDeriving d = return ()

\end{verbatim}
First, the compiler adds all explicit instance declarations to the
instance environment.
\begin{verbatim}

> bindInstance :: ModuleIdent -> TCEnv -> TopDecl a -> InstEnv -> InstEnv
> bindInstance m tcEnv (InstanceDecl _ cx cls ty _) =
>   bindEnv (CT cls' (rootOfType ty')) (m,cx')
>   where cls' = origName (head (qualLookupTopEnv cls tcEnv))
>         QualType cx' ty' = expandPolyType tcEnv (QualTypeExpr cx ty)
> bindInstance _ _ _ = id

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
(cf.\ Chap.~10 of~\cite{PeytonJones03:Haskell}). The context \emph{cx}
must include all class assertions appearing on the right hand side of
a data type declaration so that the correct instance context is
inferred for a declaration like
\begin{verbatim}
  data T a = Eq a => T a deriving (Bounded)
\end{verbatim}
namely \verb|(Eq a, Bounded a)|. Since no instances are derived for
existentially quantified data types, only constraints for universally
quantified type variables are considered here. In the case of
(mutually) recursive data types, inference of the appropriate contexts
may require a fixpoint calculation.

For the purpose of inferring derived instance contexts, we make no
distinction between data type and newtype declarations. Furthermore,
we are interested only in the argument types of all constructors of a
type, not the constructors themselves. The compiler also carefully
sorts derived classes with respect to the super class hierarchy so
that subclass instances are added to the instance environment after
their super classes.
\begin{verbatim}

> data Deriving =
>   Deriving Position QualIdent QualType [Type] [QualIdent]
>   deriving Show

> declDeriving :: ModuleIdent -> TCEnv -> TopDecl a -> Deriving
> declDeriving m tcEnv (DataDecl p cx tc tvs cs clss) =
>   mkDeriving m tcEnv p (cx ++ concat cxs) tc tvs (concat tyss) clss
>   where (cxs,tyss) = unzip (map constrTypes cs)
>         constrTypes (ConstrDecl _ _ cx _ tys) = (cx,tys)
>         constrTypes (ConOpDecl _ _ cx ty1 _ ty2) = (cx,[ty1,ty2])
>         constrTypes (RecordDecl _ _ cx _ fs) = (cx,tys)
>           where tys = [ty | FieldDecl _ ls ty <- fs, l <- ls]
> declDeriving m tcEnv (NewtypeDecl p cx tc tvs nc clss) =
>   mkDeriving m tcEnv p cx tc tvs [nconstrType nc] clss
>   where nconstrType (NewConstrDecl _ _ ty) = ty
>         nconstrType (NewRecordDecl _ _ _ ty) = ty

> mkDeriving :: ModuleIdent -> TCEnv -> Position -> [ClassAssert] -> Ident
>            -> [Ident] -> [TypeExpr] -> [DClass] -> Deriving
> mkDeriving m tcEnv p cx tc tvs tys dclss =
>   Deriving p tc' (QualType cx' ty'') tys' (sortClasses tcEnv clss)
>   where tc' = qualifyWith m tc
>         clss = [cls | DClass _ cls <- dclss]
>         (tys',ty'') = arrowUnapply ty'
>         QualType cx' ty' = snd (expandConstrType tcEnv cx tc' tvs [] tys)

> sortClasses :: TCEnv -> [QualIdent] -> [QualIdent]
> sortClasses tcEnv clss =
>   map fst (sortBy compareDepth (map (adjoinDepth tcEnv) clss))
>   where (_,d1) `compareDepth` (_,d2) = d1 `compare` d2
>         adjoinDepth tcEnv cls = (cls,length (allSuperClasses cls tcEnv))

\end{verbatim}
After adding all explicit instance declarations to the instance
environment, the compiler sorts the data and newtype declarations with
non-empty deriving clauses into minimal binding groups and infers
contexts for their instance declarations.
\begin{verbatim}

> bindDerivedInstances :: ModuleIdent -> TCEnv -> InstEnv -> [Deriving]
>                      -> Error InstEnv
> bindDerivedInstances m tcEnv iEnv [Deriving p tc ty tys clss]
>   | tc `notElem` ft tys = foldM (bindDerived m tcEnv p tc ty tys) iEnv clss
> bindDerivedInstances m tcEnv iEnv ds =
>   foldM (bindInitialContexts m tcEnv) iEnv ds >>=
>   fixpoint (\iEnv' -> updateContexts iEnv' . concat)
>            (\iEnv' -> mapE (inferContexts tcEnv iEnv') ds)
>   where fixpoint f m x = m x >>= maybe (return x) (fixpoint f m) . f x

> bindDerived :: ModuleIdent -> TCEnv -> Position -> QualIdent -> QualType
>             -> [Type] -> InstEnv -> QualIdent -> Error InstEnv
> bindDerived m tcEnv p tc ty tys iEnv cls =
>   liftM (bindInstance m iEnv) (inferContext tcEnv iEnv p tc ty tys cls)
>   where bindInstance m iEnv (ct,cx) = bindEnv ct (m,cx) iEnv

> bindInitialContexts :: ModuleIdent -> TCEnv -> InstEnv -> Deriving
>                     -> Error InstEnv
> bindInitialContexts m tcEnv iEnv (Deriving p tc ty _ clss) =
>   foldM (bindDerived m tcEnv p tc ty []) iEnv clss

> inferContexts :: TCEnv -> InstEnv -> Deriving -> Error [(CT,Context)]
> inferContexts tcEnv iEnv (Deriving p tc ty tys clss) =
>   mapE (inferContext tcEnv iEnv p tc ty tys) clss

> inferContext :: TCEnv -> InstEnv -> Position -> QualIdent -> QualType
>              -> [Type] -> QualIdent -> Error (CT,Context)
> inferContext tcEnv iEnv p tc (QualType cx ty) tys cls =
>   do
>     cx'' <- reduceContext p what doc tcEnv iEnv cx'
>     mapE_ (reportUndecidable p what doc tcEnv) cx''
>     return (CT cls' tc,sort cx'')
>   where what = "derived instance"
>         doc = ppInstance tcEnv (TypePred cls ty)
>         (cls',clss) =
>           case qualLookupTopEnv cls tcEnv of
>             [TypeClass cls' _ clss _] -> (cls',clss)
>             _ -> internalError "inferContext"
>         cx' = nub (cx ++ [TypePred cls ty | cls <- clss] ++
>                    [TypePred cls' ty | ty <- tys])

> updateContexts :: InstEnv -> [(CT,Context)] -> Maybe InstEnv
> updateContexts iEnv cxs = if or upds then Just iEnv' else Nothing
>   where (iEnv',upds) = mapAccumL updateInstance iEnv cxs
>         updateInstance iEnv (ct,cx) =
>           case lookupEnv ct iEnv of
>             Just (m,cx')
>               | cx == cx' -> (iEnv,False)
>               | otherwise -> (bindEnv ct (m,cx) iEnv,True)
>             Nothing -> internalError "updateContext"

> sortDeriving :: [Deriving] -> [[Deriving]]
> sortDeriving ds = scc bound free ds
>   where bound (Deriving _ tc _ _ _) = [tc]
>         free (Deriving _ _ _ tys _) = ft tys

> ft :: [Type] -> [QualIdent]
> ft tys = foldr types [] tys
>   where types (TypeConstructor tc) = (tc :)
>         types (TypeVariable _) = id
>         types (TypeConstrained _ _) = id
>         types (TypeSkolem _) = id
>         types (TypeApply ty1 ty2) = types ty1 . types ty2
>         types (TypeArrow ty1 ty2) = types ty1 . types ty2

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

\end{verbatim}
All types specified in the optional default declaration of a module
must be instances of the \texttt{Num} class. Since these types are
used to resolve ambiguous type variables, the contexts of the
respective instances must be empty.
\begin{verbatim}

> checkDefault :: TCEnv -> InstEnv -> TopDecl a -> Error ()
> checkDefault tcEnv iEnv (DefaultDecl p tys) =
>   mapE_ (checkDefaultType tcEnv iEnv p) tys

> checkDefaultType :: TCEnv -> InstEnv -> Position -> TypeExpr -> Error ()
> checkDefaultType tcEnv iEnv p ty =
>   do
>     cx' <- reduceContext p what empty tcEnv iEnv [TypePred qNumId ty']
>     unless (null cx') (mapE_ (errorAt p . noInstance what empty tcEnv) cx')
>   where what = "default declaration"
>         QualType _ ty' = expandPolyType tcEnv (QualTypeExpr [] ty)

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
>   maybe [TypePred cls ty] (reduceTypePreds iEnv) (instContext iEnv cls ty)

> instContext :: InstEnv -> QualIdent -> Type -> Maybe Context
> instContext iEnv cls ty =
>   case unapplyType False ty of
>     (TypeConstructor tc,tys) ->
>       fmap (map (expandAliasType tys) . snd) (lookupEnv (CT cls tc) iEnv)
>     _ -> Nothing

> partitionContext :: Context -> (Context,Context)
> partitionContext cx = partition (\(TypePred _ ty) -> isTypeVar ty) cx
>   where isTypeVar (TypeConstructor _) = False
>         isTypeVar (TypeVariable _) = True
>         isTypeVar (TypeConstrained _ _) = False
>         isTypeVar (TypeSkolem _) = False
>         isTypeVar (TypeApply ty _) = isTypeVar ty
>         isTypeVar (TypeArrow _ _) = False

\end{verbatim}
Constraints in instance contexts are restricted to the form $C\,u$,
where $u$ is a type variable. The rationale behind this restriction is
that it ensures termination of context reduction. For instance,
consider the definition
\begin{verbatim}
  data T f a = U a | T (f (T f a))
\end{verbatim}
A derived \texttt{Eq} instance declaration for this type would have
context \texttt{(Eq a, Eq (f (T f a)))}. If this equality instance is
used for $\texttt{f}=\texttt{[]}$, a new \texttt{Eq (T [] a)}
constraint enters the context whenever a constraint \texttt{Eq (T []
a)} is reduced. In order to prevent this infinite recursion, we comply
strictly to the revised Haskell'98 report~\cite{PeytonJones03:Haskell}
(cf.\ Sect.~4.3.2) and report an error when a constraint that does
not have the form $C\,u$ is found in the context of a derived
instance.
\begin{verbatim}

> reportUndecidable :: Position -> String -> Doc -> TCEnv -> TypePred-> Error ()
> reportUndecidable p what doc tcEnv (TypePred cls ty) =
>   case ty of
>     TypeVariable _ -> return ()
>     _ -> errorAt p (invalidConstraint what doc tcEnv (TypePred cls ty))

\end{verbatim}
Error functions.
\begin{verbatim}

> noInstance :: String -> Doc -> TCEnv -> TypePred -> String
> noInstance what doc tcEnv tp = show $
>   text "Missing" <+> ppInstance tcEnv tp <+> text "instance" $$
>   text "in" <+> text what <+> doc

> invalidConstraint :: String -> Doc -> TCEnv -> TypePred -> String
> invalidConstraint what doc tcEnv tp = show $
>   text "Illegal class constraint" <+> ppInstance tcEnv tp $$
>   text "in" <+> text what <+> doc

> noAbstractDerive :: String
> noAbstractDerive = "Instances cannot be derived for abstract types"

> noExistentialDerive :: String
> noExistentialDerive =
>   "Instances cannot be derived for existentially quantified types"

\end{verbatim}
