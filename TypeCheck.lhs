% -*- LaTeX -*-
% $Id: TypeCheck.lhs 2070 2007-01-13 22:35:41Z wlux $
%
% Copyright (c) 1999-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{TypeCheck.lhs}
\section{Type Inference}
This module implements the type checker of the Curry compiler. The
type checker is invoked after the syntactic correctness of the program
has been verified and kind checking has been applied to all type
expressions. Local variables have been renamed already. Therefore, the
compiler can maintain a flat type environment (which is necessary in
order to pass the type information to later phases of the compiler).
The type checker now checks the correct typing of all expressions and
also verifies that the type signatures given by the user match the
inferred types. The type checker uses algorithm
W~\cite{DamasMilner82:Principal} for inferring the types of
unannotated declarations, but allows for polymorphic recursion when a
type annotation is present.
\begin{verbatim}

> module TypeCheck(typeCheck,typeCheckGoal) where
> import Base
> import Pretty
> import CurryPP
> import Env
> import TopEnv
> import TypeSubst
> import TypeTrans
> import Combined
> import Error
> import List
> import Maybe
> import Monad
> import SCC
> import Set
> import Utils

> infixl 5 $-$

> ($-$) :: Doc -> Doc -> Doc
> x $-$ y = x $$ space $$ y

\end{verbatim}
Before checking the function declarations of a module, the compiler
adds the types of all data and newtype constructors defined in the
current module into the type environment.
\begin{verbatim}

> typeCheck :: ModuleIdent -> TCEnv -> InstEnv -> ValueEnv -> [TopDecl a]
>           -> Error (ValueEnv,[TopDecl Type])
> typeCheck m tcEnv iEnv tyEnv ds =
>   run (do
>          (cx,vds') <- tcDecls m tcEnv [d | BlockDecl d <- vds]
>          unless (null cx) (internalError ("typeCheck " ++ show cx))
>          tds' <- mapM (tcTopDecl m tcEnv) tds
>          tyEnv' <- fetchSt
>          theta <- liftSt fetchSt
>          return (subst theta tyEnv',
>                  map (fmap (subst theta)) (tds' ++ map BlockDecl vds')))
>       iEnv
>       (foldr (bindTypeValues m tcEnv) tyEnv tds)
>   where (vds,tds) = partition isBlockDecl ds

\end{verbatim}
Type checking of a goal is simpler because there are no type
declarations. Depending on whether we only compute the type of a goal
or a going to generate code for the goal, the compiler will allow a
non-empty context for the goal's type or not.
\begin{verbatim}

> typeCheckGoal :: Bool -> TCEnv -> InstEnv -> ValueEnv -> Goal a
>               -> Error (ValueEnv,Context,Goal Type)
> typeCheckGoal forEval tcEnv iEnv tyEnv g =
>   run (do
>          (cx,g') <- tcGoal forEval emptyMIdent tcEnv g
>          tyEnv' <- fetchSt
>          theta <- liftSt fetchSt
>          return (subst theta tyEnv',cx,fmap (subst theta) g'))
>       iEnv
>       tyEnv

\end{verbatim}
The type checker makes use of nested state monads in order to
maintain the type environment, the current substitution, and a counter
which is used for generating fresh type variables. In addition, the
instance environment is passed around using a reader monad.
\begin{verbatim}

> type TcState a =
>   StateT ValueEnv (StateT TypeSubst (ReaderT InstEnv (StateT Int Error))) a

> run :: TcState a -> InstEnv -> ValueEnv -> Error a
> run m iEnv tyEnv = callSt (callRt (callSt (callSt m tyEnv) idSubst) iEnv) 1

\end{verbatim}
\paragraph{Defining Data Constructors and Methods}
First, the types of all data and newtype constructors as well as those
of all type class methods are entered into the type environment. All
type synonyms occurring in their types are expanded.
\begin{verbatim}

> bindTypeValues :: ModuleIdent -> TCEnv -> TopDecl a -> ValueEnv -> ValueEnv
> bindTypeValues m tcEnv (DataDecl _ cx tc tvs cs _) tyEnv = foldr bind tyEnv cs
>   where bind (ConstrDecl _ _ c tys) =
>           bindConstr DataConstructor m tcEnv cx tc tvs c tys
>         bind (ConOpDecl _ _ ty1 op ty2) =
>           bindConstr DataConstructor m tcEnv cx tc tvs op [ty1,ty2]
> bindTypeValues m tcEnv (NewtypeDecl _ cx tc tvs nc _) tyEnv = bind nc tyEnv
>   where bind (NewConstrDecl _ c ty) =
>           bindConstr NewtypeConstructor m tcEnv cx tc tvs c [ty]
> bindTypeValues _ _ (TypeDecl _ _ _ _) tyEnv = tyEnv
> bindTypeValues m tcEnv (ClassDecl _ _ cls tv ds) tyEnv = foldr bind tyEnv ds
>   where cx = [ClassAssert (qualifyWith m cls) tv]
>         bind (MethodFixity _ _ _ _) = id
>         bind (MethodSig _ fs ty) = bindMethods m tcEnv cx fs ty
>         bind (MethodDecl _ _ _) = id
>         bind (TrustMethod _ _ _) = id
> bindTypeValues _ _ (InstanceDecl _ _ _ _ _) tyEnv = tyEnv
> bindTypeValues _ _ (BlockDecl _) tyEnv = tyEnv

> bindConstr :: (QualIdent -> TypeScheme -> ValueInfo) -> ModuleIdent
>            -> TCEnv -> [ClassAssert] -> Ident -> [Ident] -> Ident
>            -> [TypeExpr] -> ValueEnv -> ValueEnv
> bindConstr f m tcEnv cx tc tvs c tys =
>   globalBindTopEnv m c (f (qualifyWith m c) (typeScheme ty))
>   where ty = expandConstrType tcEnv cx (qualifyWith m tc) tvs tys

> bindMethods :: ModuleIdent -> TCEnv -> [ClassAssert] -> [Ident] -> TypeExpr
>             -> ValueEnv -> ValueEnv
> bindMethods m tcEnv cx fs ty tyEnv = foldr (bindMethod m ty') tyEnv fs
>   where ty' = expandPolyType tcEnv (QualTypeExpr cx ty)

> bindMethod :: ModuleIdent -> TypeScheme -> Ident -> ValueEnv -> ValueEnv
> bindMethod m ty f = globalBindTopEnv m f (Value (qualifyWith m f) ty)

\end{verbatim}
\paragraph{Type Signatures}
The type checker collects type signatures in a flat environment. The
types are not expanded so that the signatures can be used in the error
messages, which are printed when an inferred type is less general than
the signature.
\begin{verbatim}

> type SigEnv = Env Ident QualTypeExpr

> noSigs :: SigEnv
> noSigs = emptyEnv

> bindTypeSigs :: Decl a -> SigEnv -> SigEnv
> bindTypeSigs (TypeSig _ vs ty) env = foldr (flip bindEnv ty) env vs 
> bindTypeSigs _ env = env
        
\end{verbatim}
\paragraph{Declaration Groups}
Before type checking a group of declarations, a dependency analysis is
performed and the declaration group is split into minimal, nested
binding groups which are checked separately. Within each binding
group, first the left hand sides of all declarations are typed
introducing new bindings for their bound variables. Next, the right
hand sides of the declarations are typed in the extended type
environment and the inferred types are unified with the left hand side
types. Finally, the types of all defined functions are generalized.
The generalization step will also check that the type signatures given
by the user match the inferred types.

Since expressions can contain shared logical variables, one has to be
careful when generalizing the types of local variables. For instance,
if the types of local variables were always generalized, the unsound
function
\begin{verbatim}
  bug = x =:= 1 & x =:= 'a' where x = unknown
\end{verbatim}
would be accepted because the type $\forall\alpha.\alpha$ would be
assigned to \verb|x|.\footnote{The function \texttt{unknown = x where
    x free} is defined in the Curry prelude and has type
  $\forall\alpha.\alpha$.} In order to reject such unsound programs,
the type checker does not generalize the types of local variables.
Note that by this policy, some perfectly valid declarations like,
e.g.,
\begin{verbatim}
  ok = (1:nil, 'a':nil) where nil = []
\end{verbatim}
are rejected. This could be avoided by adopting ML's value
restriction~\cite{WrightFelleisen94:TypeSoundness,
  Garrigue04:ValueRestriction}. However, in contrast to ML, the
distinction between expansive and non-expansive expressions cannot be
purely syntactic in Curry because it is possible to define nullary
functions at the top-level. An expression $f$ would be expansive if
$f$ is a nullary function and non-expansive otherwise.

Within a group of mutually recursive declarations, all type variables
that appear in the types of the variables defined in the group must
not be generalized. Without this restriction, the compiler would
accept the function
\begin{verbatim}
  illTyped = x=:=1 &> f True "Hello"
    where (x:xs) = f True (repeat unknown)
          f _ [] = []
          f b (y:ys) = (if b then y else x) : f (not b) ys
\end{verbatim}
whose result is the ill-typed list \verb|['H',1,'l',1,'o']|,
because \verb|f|'s type would incorrectly be generalized to
$\forall\alpha.\texttt{Bool}\rightarrow[\alpha]\rightarrow[\alpha]$.

Note that \texttt{tcFunctionDecl} ignores the context of a function's
type signature. This prevents spurious missing instance errors when
the inferred type of a function is less general than the declared
type. For instance, if the type signature's context were merged with
the inferred context, the compiler would report a missing instance
\texttt{Prelude.Eq (a -> a)} for the declaration
\begin{verbatim}
  f :: Eq a => a
  f = id
\end{verbatim}
instead of reporting that the inferred type \texttt{a -> a} is less
general than the type signature.
\begin{verbatim}

> tcDecls :: ModuleIdent -> TCEnv -> [Decl a] -> TcState (Context,[Decl Type])
> tcDecls m tcEnv ds =
>   do
>     (cx,dss') <-
>       mapAccumM (tcDeclGroup m tcEnv (foldr bindTypeSigs noSigs ods)) []
>                 (scc bv (qfv m) vds)
>     return (cx,map untyped ods ++ concat dss')
>   where (vds,ods) = partition isValueDecl ds

> tcDeclGroup :: ModuleIdent -> TCEnv -> SigEnv -> Context -> [Decl a]
>             -> TcState (Context,[Decl Type])
> tcDeclGroup m tcEnv _ cx [ForeignDecl p cc ie f ty] =
>   do
>     tcForeignFunct m tcEnv p cc ie f ty
>     return (cx,[ForeignDecl p cc ie f ty])
> tcDeclGroup m tcEnv sigs cx [FreeDecl p vs] =
>   do
>     mapM_ (tcDeclVar (checkMonoType p) m tcEnv sigs) vs
>     return (cx,[FreeDecl p vs])
> tcDeclGroup m tcEnv sigs cx ds =
>   do
>     tyEnv0 <- fetchSt
>     mapM_ (tcDeclVars m tcEnv sigs) ds
>     (cx',ds') <- mapAccumM (tcDecl m tcEnv) cx ds
>     tyEnv <- fetchSt
>     theta <- liftSt fetchSt
>     let tvss = map (typeVars . subst theta . flip varType tyEnv) vs
>         fvs = foldr addToSet (fvEnv (subst theta tyEnv0)) (concat tvss)
>         (gcx,lcx) = splitContext fvs cx'
>     ds'' <- mapM (uncurry3 (dfltDecl tcEnv) . mergeContext lcx theta) ds'
>     mapM_ (uncurry3 (\cx -> genDecl m tcEnv sigs . gen fvs cx)) ds''
>     return (gcx,map thd3 ds'')
>   where vs = [v | PatternDecl _ t _ <- ds, v <- bv t]
>         mergeContext cx1 theta (cx2,ty,d) = (cx1 ++ cx2,subst theta ty,d)

> tcDeclVars :: ModuleIdent -> TCEnv -> SigEnv -> Decl a -> TcState ()
> tcDeclVars m tcEnv sigs (FunctionDecl p f _) =
>   tcDeclVar (const return) m tcEnv sigs f
> tcDeclVars m tcEnv sigs (PatternDecl p t _) =
>   mapM_ (tcDeclVar (checkMonoType p) m tcEnv sigs) (bv t)

> tcDeclVar :: (Ident -> TypeScheme -> TcState TypeScheme) -> ModuleIdent
>           -> TCEnv -> SigEnv -> Ident -> TcState ()
> tcDeclVar checkType m tcEnv sigs v =
>   maybe (liftM monoType freshTypeVar) (checkType v . expandPolyType tcEnv)
>         (lookupEnv v sigs) >>=
>   updateSt_ . bindFun m v

> checkMonoType :: Monad m => Position -> Ident -> TypeScheme -> m TypeScheme
> checkMonoType p v ty
>   | isMonoType ty = return ty
>   | otherwise = errorAt p (polymorphicVar v)
>   where isMonoType (ForAll n _) = n == 0

> tcDecl :: ModuleIdent -> TCEnv -> Context -> Decl a
>        -> TcState (Context,(Context,Type,Decl Type))
> tcDecl m tcEnv cx (FunctionDecl p f eqs) =
>   do
>     tyEnv0 <- fetchSt
>     (cx',(ty',d')) <-
>       tcFunctionDecl "function" m tcEnv cx (varType f tyEnv0) p f eqs
>     theta <- liftSt fetchSt
>     let (gcx,lcx) = splitContext (fvEnv (subst theta tyEnv0)) cx'
>     return (gcx,(lcx,ty',d'))
> tcDecl m tcEnv cx d@(PatternDecl p t rhs) =
>   do
>     tyEnv0 <- fetchSt
>     (cx',ty',t') <- tcConstrTerm (lookupType tyEnv0) tcEnv p t
>     (cx'',rhs') <-
>       tcRhs m tcEnv rhs >>=
>       unifyDecl p "pattern declaration" (ppDecl d) tcEnv tyEnv0 (cx++cx') ty'
>     return (cx'',([],ty',PatternDecl p t' rhs'))
>   where lookupType tyEnv v = inst (varType v tyEnv)

> tcFunctionDecl :: String -> ModuleIdent -> TCEnv -> Context -> TypeScheme
>                -> Position -> Ident -> [Equation a]
>                -> TcState (Context,(Type,Decl Type))
> tcFunctionDecl what m tcEnv cx ty p f eqs =
>   do
>     tyEnv0 <- fetchSt
>     theta <- liftSt fetchSt
>     (_,ty') <- inst ty
>     (cxs,eqs') <- liftM unzip $
>       mapM (tcEquation m tcEnv (fsEnv (subst theta tyEnv0)) ty' f) eqs
>     reduceContext p (what ++ " declaration") (ppDecl (FunctionDecl p f eqs))
>                   tcEnv (cx ++ concat cxs) (ty',FunctionDecl p f eqs')

> tcEquation :: ModuleIdent -> TCEnv -> Set Int -> Type -> Ident -> Equation a
>            -> TcState (Context,Equation Type)
> tcEquation m tcEnv fs ty f eq@(Equation p lhs rhs) =
>   do
>     tyEnv0 <- fetchSt
>     cx <-
>       tcEqn m tcEnv p lhs rhs >>=
>       unifyDecl p "function declaration" (ppEquation eq) tcEnv tyEnv0 [] ty
>     checkSkolems p tcEnv (text "Function:" <+> ppIdent f) fs ty
>     return cx

> tcEqn :: ModuleIdent -> TCEnv -> Position -> Lhs a -> Rhs a
>       -> TcState (Context,Type,Equation Type)
> tcEqn m tcEnv p lhs rhs =
>   do
>     (cx,tys,lhs') <- tcLhs m tcEnv p lhs
>     (cx',ty,rhs') <- tcRhs m tcEnv rhs
>     return (cx ++ cx',foldr TypeArrow ty tys,Equation p lhs' rhs')

> tcGoal :: Bool -> ModuleIdent -> TCEnv -> Goal a
>        -> TcState (Context,Goal Type)
> tcGoal forEval m tcEnv (Goal p e ds) =
>   do
>     tyEnv0 <- fetchSt
>     alpha <- freshTypeVar
>     (cx,SimpleRhs _ e' ds') <-
>       tcRhs m tcEnv (SimpleRhs p e ds) >>=
>       unifyDecl p "goal" (ppExpr 0 e) tcEnv tyEnv0 [] alpha
>     theta <- liftSt fetchSt
>     let ty = subst theta alpha
>         tvs = if forEval then zeroSet else fromListSet (typeVars ty)
>     checkSkolems p tcEnv (text "Goal:" <+> ppExpr 0 e) tvs ty
>     cx' <- applyDefaults p "goal" (ppExpr 0 e) tcEnv tvs cx ty
>     return (cx',Goal p e' ds')

> unifyDecl :: Position -> String -> Doc -> TCEnv -> ValueEnv -> Context -> Type
>           -> (Context,Type,a) -> TcState (Context,a)
> unifyDecl p what doc tcEnv tyEnv0 cxLhs tyLhs (cxRhs,tyRhs,x) =
>   do
>     cx <- liftM fst $ unify p what doc tcEnv tyLhs (cxLhs ++ cxRhs,tyRhs,())
>     theta <- liftSt fetchSt
>     let ty = subst theta tyLhs
>         fvs = foldr addToSet (fvEnv (subst theta tyEnv0)) (typeVars ty)
>     cx' <- applyDefaults p what doc tcEnv fvs cx ty
>     return (cx',x)

\end{verbatim}
After inferring types for a group of mutually recursive declarations
and computing the set of its constrained type variables, the compiler
has to be prepared for some of the constrained type variables to not
appear in some of the inferred types, i.e., there may be ambiguous
types that have not been reported by \texttt{unifyDecl} above at the
level of individual function equations and pattern declarations. For
instance, given the two functions
\begin{verbatim}
  f1 [] = []
  f1 (x:xs) = if x < 0 then f2 1 xs else x : f1 xs

  f2 _ [] = []
  f2 n (x:xs) = if x < 0 then f2 (n + 1) xs else x : f1 xs
\end{verbatim}
the compiler infers types $\alpha_1 \rightarrow \alpha_1$ and
$\beta_1 \rightarrow \alpha_1 \rightarrow \alpha_1$ for \texttt{f1}
and \texttt{f2}, respectively. In addition, the constraints
$\texttt{Num}\,\alpha_1, \texttt{Ord}\,\alpha_1,
\texttt{Num}\,\beta_1$ are inferred, which means that \texttt{f1}'s
type is ambiguous because $\beta_1$ does not appear in its
type.

In~\cite{Jones99:THiH}, constrained type variables that do not appear
in the types of all (implicitly typed) equations of a binding group
are not generalized. Instead Haskell's default rules are employed in
order to resolve these ambiguous types. However, this means that the
compiler may fix $\beta_1$ prematurely to the default numeric type,
which would prevent using \texttt{f2} (consistently) at another
numeric type in the rest of the program. On the other hand, if we
delay type resolution like for the types of bound variables, we may
end up with some unresolved constraints after typing the whole module
and with no good place for reporting the error.

Fortunately there is a better solution, which is also implemented by
ghc, hbc, and nhc98. We can simply generalize the type variable
$\beta_1$ in \texttt{f2}'s type and apply default resolution to
$\beta_1$ locally in function \texttt{f1}. This is implemented in
function \texttt{dfltDecl} below. After resolving ambiguous type
variables in the type of a function declaration, this function
restores the old substitution and applies the substitution that fixes
the ambiguous type variables to the function's type annotations only.

A minor complication arises from explicitly typed declarations in a
binding group. The compiler creates a fresh instance of its type
signature at every place where an explicitly typed function is used,
including the left hand side of its own declaration. The constraints
that apply to these fresh type variables must not be considered in
other declarations when checking for ambiguous types. Nevertheless,
they must be taken into account when checking that the inferred type
is not less general than the type signature in \texttt{genDecl} below.
For that reason the inferred context of a function is split in the
\texttt{FunctionDecl} case of \texttt{tcDecl} above into a global
part, which applies to other declarations in the same binding group as
well, and a local part, which applies only to the particular
declaration.  These two parts are merged again before applying
\texttt{dfltDecl} to the types.
\begin{verbatim}

> dfltDecl :: TCEnv -> Context -> Type -> Decl Type
>          -> TcState (Context,Type,Decl Type)
> dfltDecl tcEnv cx ty (FunctionDecl p f eqs) =
>   do
>     theta <- liftSt fetchSt
>     cx' <- applyDefaults p what empty tcEnv (fromListSet (typeVars ty)) cx ty
>     theta' <- liftSt (changeSt theta)
>     return (cx',ty,fmap (subst theta') (FunctionDecl p f eqs))
>   where what = "function " ++ name f
> dfltDecl _ cx ty (PatternDecl p t rhs) = return (cx,ty,PatternDecl p t rhs)

\end{verbatim}
The code in \texttt{genDecl} below verifies that the inferred type of
a function matches its declared type. Since the type inferred for the
left hand side of a function or variable declaration is an instance of
its declared type -- provided a type signature is given -- it can only
be more specific. Therefore, if the inferred type does not match the
type signature the declared type must be too general. Note that it is
possible that the inferred context is only a subset of the declared
context because the context of a function's type signature is
(deliberately) ignored in \texttt{tcFunctionDecl} above. No check is
necessary for the variables in variable and other pattern declarations
because the types of variables must be monomorphic, which is checked
in \texttt{tcDeclVar} and \texttt{checkMonoType} above.
\begin{verbatim}

> genDecl :: ModuleIdent -> TCEnv -> SigEnv -> TypeScheme -> Decl a
>         -> TcState ()
> genDecl m tcEnv sigs sigma (FunctionDecl p f _) =
>   case lookupEnv f sigs of
>     Just sigTy
>       | sigma `matchesTypeSig` expandPolyType tcEnv sigTy -> return ()
>       | otherwise -> errorAt p (typeSigTooGeneral tcEnv what sigTy sigma)
>     Nothing -> updateSt_ (rebindFun m f sigma)
>   where what = text "Function:" <+> ppIdent f
> genDecl _ _ _ _ (PatternDecl _ _ _) = return ()

> matchesTypeSig :: TypeScheme -> TypeScheme -> Bool
> ForAll _ (QualType cx ty) `matchesTypeSig` ForAll _ (QualType sigCx sigTy) =
>   ty == sigTy && all (`elem` sigCx) cx

\end{verbatim}
\paragraph{Class and instance declarations}
When checking method implementations in class and instance
declarations, the compiler must check that the inferred type matches
the method's declared type. This is straight forward in class
declarations (the only difference with respect to an overloaded
function with an explicit type signature is that a class method's type
signature is composed of its declared type signature and the context
from the class declaration), but a little bit more complicated for
instance declarations because the instance type must be substituted
for the type variable used in the type class declaration.
\begin{verbatim}

> tcTopDecl :: ModuleIdent -> TCEnv -> TopDecl a -> TcState (TopDecl Type)
> tcTopDecl _ _ (DataDecl p cx tc tvs cs clss) =
>   return (DataDecl p cx tc tvs cs clss)
> tcTopDecl _ _ (NewtypeDecl p cx tc tvs nc clss) =
>   return (NewtypeDecl p cx tc tvs nc clss)
> tcTopDecl _ _ (TypeDecl p tc tvs ty) = return (TypeDecl p tc tvs ty)
> tcTopDecl m tcEnv (ClassDecl p cx cls tv ds) =
>   do
>     vds' <- mapM (tcClassMethodDecl m tcEnv sigs) vds
>     return (ClassDecl p cx cls tv (map untyped ods ++ vds'))
>   where cx' = ClassAssert (qualify cls) tv : cx
>         sigs = foldr (bindTypeSigs . typeSig cx') noSigs ods
>         (vds,ods) = partition isMethodDecl ds
>         typeSig _ (MethodFixity p fix pr ops) = InfixDecl p fix pr ops
>         typeSig cx (MethodSig p fs ty) = TypeSig p fs (QualTypeExpr cx ty)
>         typeSig _ (TrustMethod p tr fs) = TrustAnnot p tr fs
> tcTopDecl m tcEnv (InstanceDecl p cx cls ty ds) =
>   do
>     vds' <- mapM (tcInstMethodDecl m tcEnv cls' ty') vds
>     return (InstanceDecl p cx cls ty (map untyped ods ++ vds'))
>   where cls' = origName (head (qualLookupTopEnv cls tcEnv))
>         ty' = expandPolyType tcEnv (QualTypeExpr cx ty)
>         (vds,ods) = partition isMethodDecl ds
> tcTopDecl _ _ (BlockDecl _) = internalError "tcTopDecl"

> tcClassMethodDecl :: ModuleIdent -> TCEnv -> SigEnv -> MethodDecl a
>                   -> TcState (MethodDecl Type)
> tcClassMethodDecl m tcEnv sigs d =
>   do
>     (ty',d') <- tcMethodDecl m tcEnv (expandPolyType tcEnv sigTy) d
>     checkClassMethodType tcEnv sigTy ty' d'
>   where sigTy = classMethodType sigs d

> checkClassMethodType :: TCEnv -> QualTypeExpr -> TypeScheme -> Decl Type
>                      -> TcState (MethodDecl Type)
> checkClassMethodType tcEnv sigTy sigma (FunctionDecl p f eqs)
>   | sigma `matchesTypeSig` expandPolyType tcEnv sigTy =
>       return (MethodDecl p f eqs)
>   | otherwise = errorAt p (typeSigTooGeneral tcEnv what sigTy sigma)
>   where what = text "Method:" <+> ppIdent f

> tcInstMethodDecl :: ModuleIdent -> TCEnv -> QualIdent -> TypeScheme
>                  -> MethodDecl a -> TcState (MethodDecl Type)
> tcInstMethodDecl m tcEnv cls instTy d =
>   do
>     methTy <- liftM (instMethodType cls instTy d) fetchSt
>     (ty',d') <- tcMethodDecl m tcEnv methTy d
>     checkInstMethodType tcEnv methTy ty' d'

> checkInstMethodType :: TCEnv -> TypeScheme -> TypeScheme -> Decl Type
>                     -> TcState (MethodDecl Type)
> checkInstMethodType tcEnv methTy sigma (FunctionDecl p f eqs)
>   | sigma `matchesTypeSig` methTy = return (MethodDecl p f eqs)
>   | otherwise = errorAt p (methodSigTooGeneral tcEnv what methTy sigma)
>   where what = text "Method:" <+> ppIdent f

\end{verbatim}
The functions \texttt{classMethodType} and \texttt{instMethodType}
return the type of a class method and an instance method,
respectively. While we can simply look up the type of a class method
among the type signatures of its class declaration, computing the type
of an instance method is a little bit more complicated. The compiler
first looks up the method's type in the value type environment and
then instantiates the class type variable with the instance type. We
can simply discard the context of the method's type recorded in the
type environment here (using \texttt{rawType}) because this context is
trivially satisfied by the instance declaration.
\begin{verbatim}

> classMethodType :: SigEnv -> MethodDecl a -> QualTypeExpr
> classMethodType sigs (MethodDecl _ f _) =
>   fromJust (lookupEnv (unRenameIdent f) sigs)

> instMethodType :: QualIdent -> TypeScheme -> MethodDecl a -> ValueEnv
>                -> TypeScheme
> instMethodType cls (ForAll _ (QualType cx ty)) (MethodDecl _ f _) =
>   typeScheme . normalize 0 . QualType cx . expandAliasType [ty] . methodType f
>   where methodType f = rawType . funType (qualifyLike cls (unRenameIdent f))

> tcMethodDecl :: ModuleIdent -> TCEnv -> TypeScheme -> MethodDecl a
>              -> TcState (TypeScheme,Decl Type)
> tcMethodDecl m tcEnv methTy (MethodDecl p f eqs) =
>   do
>     updateSt_ (bindFun m f methTy)
>     (cx,(ty,d')) <- tcFunctionDecl "method" m tcEnv [] methTy p f eqs
>     theta <- liftSt fetchSt
>     return (gen zeroSet cx (subst theta ty),d')

\end{verbatim}
\paragraph{Foreign Functions}
Argument and result types of foreign functions using the
\texttt{ccall} calling convention are restricted to the basic types
\texttt{Bool}, \texttt{Char}, \texttt{Int}, \texttt{Float},
\texttt{Ptr} and \texttt{FunPtr}. In addition, $\texttt{IO}\;t$ is a
legitimate result type when $t$ is either one of the basic types or
\texttt{()}. Furthermore, the type of a dynamic function wrapper must
be of the form $(\texttt{FunPtr}\;t) \rightarrow t$, where $t$ is a
valid foreign function type, and the type of a foreign address must be
either $\texttt{Ptr}\;a$ or $\texttt{FunPtr}\;a$, where $a$ is an
arbitrary type.
\begin{verbatim}

> tcForeignFunct :: ModuleIdent -> TCEnv -> Position -> CallConv
>                -> Maybe String -> Ident -> TypeExpr -> TcState ()
> tcForeignFunct m tcEnv p cc ie f ty =
>   do
>     checkForeignType cc (rawType ty')
>     updateSt_ (bindFun m f ty')
>   where ty' = expandPolyType tcEnv (QualTypeExpr [] ty)
>         checkForeignType CallConvPrimitive _ = return ()
>         checkForeignType CallConvCCall ty
>           | ie == Just "dynamic" = checkCDynCallType tcEnv p ty
>           | maybe False ('&' `elem`) ie = checkCAddrType tcEnv p ty
>           | otherwise = checkCCallType tcEnv p ty

> checkCCallType :: TCEnv -> Position -> Type -> TcState ()
> checkCCallType tcEnv p (TypeArrow ty1 ty2)
>   | isCArgType ty1 = checkCCallType tcEnv p ty2
>   | otherwise = errorAt p (invalidCType "argument" tcEnv ty1)
> checkCCallType tcEnv p ty
>   | isCRetType ty = return ()
>   | otherwise = errorAt p (invalidCType "result" tcEnv ty)

> checkCDynCallType :: TCEnv -> Position -> Type -> TcState ()
> checkCDynCallType tcEnv p (TypeArrow (TypeConstructor tc [ty1]) ty2)
>   | tc == qFunPtrId && ty1 == ty2 = checkCCallType tcEnv p ty1
> checkCDynCallType tcEnv p ty =
>   errorAt p (invalidCType "dynamic function" tcEnv ty)

> checkCAddrType :: TCEnv -> Position -> Type -> TcState ()
> checkCAddrType tcEnv p ty
>   | isCPtrType ty = return ()
>   | otherwise = errorAt p (invalidCType "static address" tcEnv ty)

> isCArgType :: Type -> Bool
> isCArgType (TypeConstructor tc []) = tc `elem` cBasicTypeId
> isCArgType (TypeConstructor tc [_]) = tc `elem` qStablePtrId:cPointerTypeId
> isCArgType _ = False

> isCRetType :: Type -> Bool
> isCRetType (TypeConstructor tc [ty])
>   | tc == qIOId = ty == unitType || isCArgType ty
> isCRetType ty = isCArgType ty

> isCPtrType :: Type -> Bool
> isCPtrType (TypeConstructor tc [_]) = tc `elem` cPointerTypeId
> isCPtrType _ = False

> cBasicTypeId, cPointerTypeId :: [QualIdent]
> cBasicTypeId = [qBoolId,qCharId,qIntId,qFloatId]
> cPointerTypeId = [qPtrId,qFunPtrId]

\end{verbatim}
\paragraph{Patterns and Expressions}
Note that overloaded literals are not supported in patterns.

\ToDo{Do not fix the type of integer literals in patterns prematurely.
  Even though we cannot handle overloaded literals in patterns, the
  compiler should accept the expression \texttt{(\char`\\ 0}
  $\rightarrow$ \texttt{success)} \texttt{::} \texttt{Float}
  $\rightarrow$ \texttt{Success} just like it accepts
  \texttt{(\char`\\ \_} $\rightarrow$ \texttt{0)} \texttt{::}
  \texttt{a} $\rightarrow$ \texttt{Float}.}
\begin{verbatim}

> tcLiteral :: Bool -> Literal -> TcState (Context,Type)
> tcLiteral _ (Char _) = return ([],charType)
> tcLiteral poly (Int _)
>   | poly = freshNumType
>   | otherwise = liftM ((,) []) (freshConstrained numTypes)
> tcLiteral poly (Float _)
>   | poly = freshFracType
>   | otherwise = liftM ((,) []) (freshConstrained fracTypes)
> tcLiteral _ (String _) = return ([],stringType)

> tcVariable :: ModuleIdent -> Ident -> TcState (Context,Type)
> tcVariable m v =
>   do
>     ty <- freshTypeVar
>     updateSt_ (bindFun m v (monoType ty))
>     return ([],ty)

> tcLhs :: ModuleIdent -> TCEnv -> Position -> Lhs a
>       -> TcState (Context,[Type],Lhs Type)
> tcLhs m tcEnv p (FunLhs f ts) =
>   do
>     (cxs,tys,ts') <-
>       liftM unzip3 $ mapM (tcConstrTerm (tcVariable m) tcEnv p) ts
>     return (concat cxs,tys,FunLhs f ts')
> tcLhs m tcEnv p (OpLhs t1 op t2) =
>   do
>     (cx1,ty1,t1') <- tcConstrTerm (tcVariable m) tcEnv p t1
>     (cx2,ty2,t2') <- tcConstrTerm (tcVariable m) tcEnv p t2
>     return (cx1 ++ cx2,[ty1,ty2],OpLhs t1' op t2')
> tcLhs m tcEnv p (ApLhs lhs ts) =
>   do
>     (cx,tys,lhs') <- tcLhs m tcEnv p lhs
>     (cxs,tys',ts') <-
>       liftM unzip3 $ mapM (tcConstrTerm (tcVariable m) tcEnv p) ts
>     return (cx ++ concat cxs,tys ++ tys',ApLhs lhs' ts')

> tcConstrTerm :: (Ident -> TcState (Context,Type)) -> TCEnv -> Position
>              -> ConstrTerm a -> TcState (Context,Type,ConstrTerm Type)
> tcConstrTerm _ _ _ (LiteralPattern _ l) =
>   do
>     (cx,ty) <- tcLiteral False l
>     return (cx,ty,LiteralPattern ty l)
> tcConstrTerm _ _ _ (NegativePattern _ l) =
>   do
>     (cx,ty) <- tcLiteral False l
>     return (cx,ty,NegativePattern ty l)
> tcConstrTerm tcVar _ _ (VariablePattern _ v) =
>   do
>     (cx,ty) <- tcVar v
>     return (cx,ty,VariablePattern ty v)
> tcConstrTerm tcVar tcEnv p t@(ConstructorPattern _ c ts) =
>   do
>     (cx,ty,ts') <- tcConstrApp tcVar tcEnv p (ppConstrTerm 0 t) c ts
>     return (cx,ty,ConstructorPattern ty c ts')
> tcConstrTerm tcVar tcEnv p t@(InfixPattern _ t1 op t2) =
>   do
>     (cx,ty,[t1',t2']) <-
>       tcConstrApp tcVar tcEnv p (ppConstrTerm 0 t) op [t1,t2]
>     return (cx,ty,InfixPattern ty t1' op t2')
> tcConstrTerm tcVar tcEnv p (ParenPattern t) =
>   do
>     (cx,ty,t') <- tcConstrTerm tcVar tcEnv p t
>     return (cx,ty,ParenPattern t')
> tcConstrTerm tcVar tcEnv p (TuplePattern ts) =
>   do
>     (cxs,tys,ts') <- liftM unzip3 $ mapM (tcConstrTerm tcVar tcEnv p) ts
>     return (concat cxs,tupleType tys,TuplePattern ts')
> tcConstrTerm tcVar tcEnv p t@(ListPattern _ ts) =
>   do
>     ty <- freshTypeVar
>     (cxs,ts') <- liftM unzip $ mapM (tcElem (ppConstrTerm 0 t) ty) ts
>     return (concat cxs,listType ty,ListPattern (listType ty) ts')
>   where tcElem doc ty t =
>           tcConstrTerm tcVar tcEnv p t >>=
>           unify p "pattern" (doc $-$ text "Term:" <+> ppConstrTerm 0 t)
>                 tcEnv ty
> tcConstrTerm tcVar tcEnv p t@(AsPattern v t') =
>   do
>     (cx,ty) <- tcVar v
>     (cx',t'') <-
>       tcConstrTerm tcVar tcEnv p t' >>=
>       unify p "pattern" (ppConstrTerm 0 t) tcEnv ty
>     return (cx ++ cx',ty,AsPattern v t'')
> tcConstrTerm tcVar tcEnv p (LazyPattern t) =
>   do
>     (cx,ty,t') <- tcConstrTerm tcVar tcEnv p t
>     return (cx,ty,LazyPattern t')

> tcConstrApp :: (Ident -> TcState (Context,Type)) -> TCEnv -> Position -> Doc
>             -> QualIdent -> [ConstrTerm a]
>             -> TcState (Context,Type,[ConstrTerm Type])
> tcConstrApp tcVar tcEnv p doc c ts =
>   do
>     tyEnv <- fetchSt
>     (cx,(tys,ty)) <- liftM (apSnd arrowUnapply) (skol (conType c tyEnv))
>     unless (length tys == n) (errorAt p (wrongArity c (length tys) n))
>     (cxs,ts') <- liftM unzip $ zipWithM (tcConstrArg tcVar tcEnv p doc) ts tys
>     return (cx ++ concat cxs,ty,ts')
>   where n = length ts

> tcConstrArg :: (Ident -> TcState (Context,Type)) -> TCEnv -> Position -> Doc
>             -> ConstrTerm a -> Type -> TcState (Context,ConstrTerm Type)
> tcConstrArg tcVar tcEnv p doc t ty =
>   tcConstrTerm tcVar tcEnv p t >>=
>   unify p "pattern" (doc $-$ text "Term:" <+> ppConstrTerm 0 t) tcEnv ty

> tcRhs :: ModuleIdent -> TCEnv -> Rhs a -> TcState (Context,Type,Rhs Type)
> tcRhs m tcEnv (SimpleRhs p e ds) =
>   do
>     (cx,ds') <- tcDecls m tcEnv ds
>     (cx',ty,e') <- tcExpr m tcEnv p e
>     return (cx ++ cx',ty,SimpleRhs p e' ds')
> tcRhs m tcEnv (GuardedRhs es ds) =
>   do
>     (cx,ds') <- tcDecls m tcEnv ds
>     gty <- guardType es
>     ty <- freshTypeVar
>     (cxs,es') <- liftM unzip $ mapM (tcCondExpr m tcEnv gty ty) es
>     return (cx ++ concat cxs,ty,GuardedRhs es' ds')
>   where guardType es
>           | length es > 1 = return boolType
>           | otherwise = freshConstrained guardTypes

> tcCondExpr :: ModuleIdent -> TCEnv -> Type -> Type -> CondExpr a
>            -> TcState (Context,CondExpr Type)
> tcCondExpr m tcEnv gty ty (CondExpr p g e) =
>   do
>     (cx,g') <- tcExpr m tcEnv p g >>= unify p "guard" (ppExpr 0 g) tcEnv gty
>     (cx',e') <-
>       tcExpr m tcEnv p e >>=
>       unify p "guarded expression" (ppExpr 0 e) tcEnv ty
>     return (cx ++ cx',CondExpr p g' e')

> tcExpr :: ModuleIdent -> TCEnv -> Position -> Expression a
>        -> TcState (Context,Type,Expression Type)
> tcExpr _ _ _ (Literal _ l) =
>   do
>     (cx,ty) <- tcLiteral True l
>     return (cx,ty,Literal ty l)
> tcExpr m tcEnv p (Variable _ v) =
>   do
>     (cx,ty) <- fetchSt >>= inst . funType v
>     return (cx,ty,Variable ty v)
> tcExpr m tcEnv p (Constructor _ c) =
>   do
>     (cx,ty) <- fetchSt >>= inst . conType c
>     return (cx,ty,Constructor ty c)
> tcExpr m tcEnv p (Typed e sig) =
>   do
>     tyEnv0 <- fetchSt
>     (cx,ty) <- inst sigma'
>     (cx',e') <-
>       tcExpr m tcEnv p e >>=
>       unifyDecl p "explicitly typed expression" (ppExpr 0 e) tcEnv tyEnv0
>                 [] ty
>     theta <- liftSt fetchSt
>     let fvs = fvEnv (subst theta tyEnv0)
>         sigma = gen fvs (snd (splitContext fvs cx')) (subst theta ty)
>     unless (sigma `matchesTypeSig` sigma')
>       (errorAt p (typeSigTooGeneral tcEnv (text "Expression:" <+> ppExpr 0 e)
>                                     sig sigma))
>     return (cx ++ cx',ty,Typed e' sig)
>   where sigma' = expandPolyType tcEnv sig
> tcExpr m tcEnv p (Paren e) =
>   do
>     (cx,ty,e') <- tcExpr m tcEnv p e
>     return (cx,ty,Paren e')
> tcExpr m tcEnv p (Tuple es) =
>   do
>     (cxs,tys,es') <- liftM unzip3 $ mapM (tcExpr m tcEnv p) es
>     return (concat cxs,tupleType tys,Tuple es')
> tcExpr m tcEnv p e@(List _ es) =
>   do
>     ty <- freshTypeVar
>     (cxs,es') <- liftM unzip $ mapM (tcElem (ppExpr 0 e) ty) es
>     return (concat cxs,listType ty,List (listType ty) es')
>   where tcElem doc ty e =
>           tcExpr m tcEnv p e >>=
>           unify p "expression" (doc $-$ text "Term:" <+> ppExpr 0 e) tcEnv ty
> tcExpr m tcEnv p (ListCompr e qs) =
>   do
>     (cxs,qs') <- liftM unzip $ mapM (tcQual m tcEnv p) qs
>     (cx,ty,e') <- tcExpr m tcEnv p e
>     return (concat cxs ++ cx,listType ty,ListCompr e' qs')
> tcExpr m tcEnv p e@(EnumFrom e1) =
>   do
>     (cx,ty) <- freshEnumType
>     (cx',e1') <-
>       tcExpr m tcEnv p e1 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) tcEnv ty
>     return (cx ++ cx',listType ty,EnumFrom e1')
> tcExpr m tcEnv p e@(EnumFromThen e1 e2) =
>   do
>     (cx,ty) <- freshEnumType
>     (cx',e1') <-
>       tcExpr m tcEnv p e1 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) tcEnv ty
>     (cx'',e2') <-
>       tcExpr m tcEnv p e2 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) tcEnv ty
>     return (cx ++ cx' ++ cx'',listType ty,EnumFromThen e1' e2')
> tcExpr m tcEnv p e@(EnumFromTo e1 e2) =
>   do
>     (cx,ty) <- freshEnumType
>     (cx',e1') <-
>       tcExpr m tcEnv p e1 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) tcEnv ty
>     (cx'',e2') <-
>       tcExpr m tcEnv p e2 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) tcEnv ty
>     return (cx ++ cx' ++ cx'',listType ty,EnumFromTo e1' e2')
> tcExpr m tcEnv p e@(EnumFromThenTo e1 e2 e3) =
>   do
>     (cx,ty) <- freshEnumType
>     (cx',e1') <-
>       tcExpr m tcEnv p e1 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) tcEnv ty
>     (cx'',e2') <-
>       tcExpr m tcEnv p e2 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) tcEnv ty
>     (cx''',e3') <-
>       tcExpr m tcEnv p e3 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e3) tcEnv ty
>     return (cx ++ cx' ++ cx'' ++ cx''',listType ty,EnumFromThenTo e1' e2' e3')
> tcExpr m tcEnv p e@(UnaryMinus e1) =
>   do
>     (cx,ty) <- freshNumType
>     (cx',e1') <-
>       tcExpr m tcEnv p e1 >>=
>       unify p "unary negation" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             tcEnv ty
>     return (cx ++ cx',ty,UnaryMinus e1')
> tcExpr m tcEnv p e@(Apply e1 e2) =
>   do
>     (cx,alpha,beta,e1') <-
>       tcExpr m tcEnv p e1 >>=
>       tcArrow p "application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>               tcEnv
>     (cx',e2') <-
>       tcExpr m tcEnv p e2 >>=
>       unify p "application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2)
>             tcEnv alpha
>     return (cx ++ cx',beta,Apply e1' e2')
> tcExpr m tcEnv p e@(InfixApply e1 op e2) =
>   do
>     (cx,alpha,beta,gamma,op') <-
>       tcInfixOp m tcEnv p op >>=
>       tcBinary p "infix application"
>                (ppExpr 0 e $-$ text "Operator:" <+> ppOp op) tcEnv
>     (cx',e1') <-
>       tcExpr m tcEnv p e1 >>=
>       unify p "infix application"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) tcEnv alpha
>     (cx'',e2') <-
>       tcExpr m tcEnv p e2 >>=
>       unify p "infix application"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) tcEnv beta
>     return (cx ++ cx' ++ cx'',gamma,InfixApply e1' op' e2')
> tcExpr m tcEnv p e@(LeftSection e1 op) =
>   do
>     (cx,alpha,beta,op') <-
>       tcInfixOp m tcEnv p op >>=
>       tcArrow p "left section" (ppExpr 0 e $-$ text "Operator:" <+> ppOp op)
>               tcEnv
>     (cx',e1') <-
>       tcExpr m tcEnv p e1 >>=
>       unify p "left section" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             tcEnv alpha
>     return (cx ++ cx',beta,LeftSection e1' op')
> tcExpr m tcEnv p e@(RightSection op e1) =
>   do
>     (cx,alpha,beta,gamma,op') <-
>       tcInfixOp m tcEnv p op >>=
>       tcBinary p "right section"
>                (ppExpr 0 e $-$ text "Operator:" <+> ppOp op) tcEnv
>     (cx',e1') <-
>       tcExpr m tcEnv p e1 >>=
>       unify p "right section" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             tcEnv beta
>     return (cx ++ cx',TypeArrow alpha gamma,RightSection op' e1')
> tcExpr m tcEnv p (Lambda ts e) =
>   do
>     (cxs,tys,ts') <-
>       liftM unzip3 $ mapM (tcConstrTerm (tcVariable m) tcEnv p) ts
>     (cx',ty,e') <- tcExpr m tcEnv p e
>     return (concat cxs ++ cx',foldr TypeArrow ty tys,Lambda ts' e')
> tcExpr m tcEnv p (Let ds e) =
>   do
>     (cx,ds') <- tcDecls m tcEnv ds
>     (cx',ty,e') <- tcExpr m tcEnv p e
>     return (cx ++ cx',ty,Let ds' e')
> tcExpr m tcEnv p (Do sts e) =
>   do
>     (cxs,sts') <- liftM unzip $ mapM (tcStmt m tcEnv p) sts
>     ty <- liftM ioType freshTypeVar
>     (cx,e') <-
>       tcExpr m tcEnv p e >>= unify p "statement" (ppExpr 0 e) tcEnv ty
>     return (concat cxs ++ cx,ty,Do sts' e')
> tcExpr m tcEnv p e@(IfThenElse e1 e2 e3) =
>   do
>     (cx,e1') <-
>       tcExpr m tcEnv p e1 >>=
>       unify p "expression" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             tcEnv boolType
>     (cx',ty,e2') <- tcExpr m tcEnv p e2
>     (cx'',e3') <-
>       tcExpr m tcEnv p e3 >>=
>       unify p "expression" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e3)
>             tcEnv ty
>     return (cx ++ cx' ++ cx'',ty,IfThenElse e1' e2' e3')
> tcExpr m tcEnv p (Case e as) =
>   do
>     (cx,tyLhs,e') <- tcExpr m tcEnv p e
>     tyRhs <- freshTypeVar
>     (cxs,as') <- liftM unzip $ mapM (tcAlt m tcEnv tyLhs tyRhs) as
>     return (cx ++ concat cxs,tyRhs,Case e' as')

> tcAlt :: ModuleIdent -> TCEnv -> Type -> Type -> Alt a
>       -> TcState (Context,Alt Type)
> tcAlt m tcEnv tyLhs tyRhs a@(Alt p t rhs) =
>   do
>     (cx,t') <-
>       tcConstrTerm (tcVariable m) tcEnv p t >>=
>       unify p "case pattern" (doc $-$ text "Term:" <+> ppConstrTerm 0 t)
>             tcEnv tyLhs
>     (cx',rhs') <- tcRhs m tcEnv rhs >>= unify p "case branch" doc tcEnv tyRhs
>     return (cx ++ cx',Alt p t' rhs')
>   where doc = ppAlt a

> tcQual :: ModuleIdent -> TCEnv -> Position -> Statement a
>        -> TcState (Context,Statement Type)
> tcQual m tcEnv p (StmtExpr e) =
>   do
>     (cx,e') <-
>       tcExpr m tcEnv p e >>= unify p "guard" (ppExpr 0 e) tcEnv boolType
>     return (cx,StmtExpr e')
> tcQual m tcEnv p q@(StmtBind t e) =
>   do
>     (cx,ty,t') <- tcConstrTerm (tcVariable m) tcEnv p t
>     (cx',e') <-
>       tcExpr m tcEnv p e >>=
>       unify p "generator" (ppStmt q $-$ text "Term:" <+> ppExpr 0 e)
>             tcEnv (listType ty)
>     return (cx ++ cx',StmtBind t' e')
> tcQual m tcEnv p (StmtDecl ds) =
>   do
>     (cx,ds') <- tcDecls m tcEnv ds
>     return (cx,StmtDecl ds')

> tcStmt :: ModuleIdent -> TCEnv -> Position -> Statement a
>        -> TcState (Context,Statement Type)
> tcStmt m tcEnv p (StmtExpr e) =
>   do
>     alpha <- freshTypeVar
>     (cx',e') <-
>       tcExpr m tcEnv p e >>=
>       unify p "statement" (ppExpr 0 e) tcEnv (ioType alpha)
>     return (cx',StmtExpr e')
> tcStmt m tcEnv p st@(StmtBind t e) =
>   do
>     (cx,ty,t') <- tcConstrTerm (tcVariable m) tcEnv p t
>     (cx',e') <-
>       tcExpr m tcEnv p e >>=
>       unify p "statement" (ppStmt st $-$ text "Term:" <+> ppExpr 0 e)
>             tcEnv (ioType ty)
>     return (cx ++ cx',StmtBind t' e')
> tcStmt m tcEnv p (StmtDecl ds) =
>   do
>     (cx,ds') <- tcDecls m tcEnv ds
>     return (cx,StmtDecl ds')

> tcInfixOp :: ModuleIdent -> TCEnv -> Position -> InfixOp a
>           -> TcState (Context,Type,InfixOp Type)
> tcInfixOp m tcEnv p (InfixOp a op) =
>   do
>     (cx,ty,_) <- tcExpr m tcEnv p (Variable a op)
>     return (cx,ty,InfixOp ty op)
> tcInfixOp m tcEnv p (InfixConstr a op) =
>   do
>     (cx,ty,_) <- tcExpr m tcEnv p (Constructor a op)
>     return (cx,ty,InfixConstr ty op)

\end{verbatim}
The function \texttt{tcArrow} checks that its argument can be used as
an arrow type $\alpha\rightarrow\beta$ and returns the pair
$(\alpha,\beta)$. Similarly, the function \texttt{tcBinary} checks
that its argument can be used as an arrow type
$\alpha\rightarrow\beta\rightarrow\gamma$ and returns the triple
$(\alpha,\beta,\gamma)$.
\begin{verbatim}

> tcArrow :: Position -> String -> Doc -> TCEnv -> (a,Type,b)
>         -> TcState (a,Type,Type,b)
> tcArrow p what doc tcEnv (x,ty,y) =
>   do
>     theta <- liftSt fetchSt
>     unaryArrow (subst theta ty)
>   where unaryArrow (TypeArrow ty1 ty2) = return (x,ty1,ty2,y)
>         unaryArrow (TypeVariable tv) =
>           do
>             alpha <- freshTypeVar
>             beta <- freshTypeVar
>             liftSt (updateSt_ (bindVar tv (TypeArrow alpha beta)))
>             return (x,alpha,beta,y)
>         unaryArrow ty = errorAt p (nonFunctionType what doc tcEnv ty)

> tcBinary :: Position -> String -> Doc -> TCEnv -> (a,Type,b)
>          -> TcState (a,Type,Type,Type,b)
> tcBinary p what doc tcEnv ty = tcArrow p what doc tcEnv ty >>= binaryArrow
>   where binaryArrow (x,ty1,TypeArrow ty2 ty3,y) = return (x,ty1,ty2,ty3,y)
>         binaryArrow (x,ty1,TypeVariable tv,y) =
>           do
>             beta <- freshTypeVar
>             gamma <- freshTypeVar
>             liftSt (updateSt_ (bindVar tv (TypeArrow beta gamma)))
>             return (x,ty1,beta,gamma,y)
>         binaryArrow (_,ty1,ty2,_) =
>           errorAt p (nonBinaryOp what doc tcEnv (TypeArrow ty1 ty2))

\end{verbatim}
\paragraph{Unification}
The unification uses Robinson's algorithm (cf., e.g., Chap.~9
of~\cite{PeytonJones87:Book}).
\begin{verbatim}

> unify :: Position -> String -> Doc -> TCEnv -> Type -> (Context,Type,a)
>       -> TcState (Context,a)
> unify p what doc tcEnv ty1 (cx,ty2,x) =
>   do
>     theta <- liftSt fetchSt
>     let ty1' = subst theta ty1
>     let ty2' = subst theta ty2
>     either (errorAt p . typeMismatch what doc tcEnv ty1' ty2')
>            (liftSt . updateSt_ . compose)
>            (unifyTypes tcEnv ty1' ty2')
>     reduceContext p what doc tcEnv cx x

> unifyTypes :: TCEnv -> Type -> Type -> Either Doc TypeSubst
> unifyTypes _ (TypeVariable tv1) (TypeVariable tv2)
>   | tv1 == tv2 = Right idSubst
>   | otherwise = Right (bindSubst tv1 (TypeVariable tv2) idSubst)
> unifyTypes tcEnv (TypeVariable tv) ty
>   | tv `elem` typeVars ty = Left (recursiveType tcEnv tv ty)
>   | otherwise = Right (bindSubst tv ty idSubst)
> unifyTypes tcEnv ty (TypeVariable tv)
>   | tv `elem` typeVars ty = Left (recursiveType tcEnv tv ty)
>   | otherwise = Right (bindSubst tv ty idSubst)
> unifyTypes _ (TypeConstrained tys1 tv1) (TypeConstrained tys2 tv2)
>   | tv1 == tv2 = Right idSubst
>   | tys1 == tys2 = Right (bindSubst tv1 (TypeConstrained tys2 tv2) idSubst)
> unifyTypes tcEnv (TypeConstrained tys tv) ty =
>   foldr (choose . unifyTypes tcEnv ty)
>         (Left (incompatibleTypes tcEnv ty (head tys)))
>         tys
>   where choose (Left _) theta' = theta'
>         choose (Right theta) _ = Right (bindSubst tv ty theta)
> unifyTypes tcEnv ty (TypeConstrained tys tv) =
>   foldr (choose . unifyTypes tcEnv ty)
>         (Left (incompatibleTypes tcEnv ty (head tys)))
>         tys
>   where choose (Left _) theta' = theta'
>         choose (Right theta) _ = Right (bindSubst tv ty theta)
> unifyTypes tcEnv (TypeConstructor tc1 tys1) (TypeConstructor tc2 tys2)
>   | tc1 == tc2 = unifyTypeLists tcEnv tys1 tys2
> unifyTypes tcEnv (TypeArrow ty11 ty12) (TypeArrow ty21 ty22) =
>   unifyTypeLists tcEnv [ty11,ty12] [ty21,ty22]
> unifyTypes _ (TypeSkolem k1) (TypeSkolem k2)
>   | k1 == k2 = Right idSubst
> unifyTypes tcEnv ty1 ty2 = Left (incompatibleTypes tcEnv ty1 ty2)

> unifyTypeLists :: TCEnv -> [Type] -> [Type] -> Either Doc TypeSubst
> unifyTypeLists _ [] _ = Right idSubst
> unifyTypeLists _ _ [] = Right idSubst
> unifyTypeLists tcEnv (ty1:tys1) (ty2:tys2) =
>   either Left (unifyTypesTheta tcEnv ty1 ty2) (unifyTypeLists tcEnv tys1 tys2)
>   where unifyTypesTheta tcEnv ty1 ty2 theta =
>           either Left (Right . flip compose theta)
>                  (unifyTypes tcEnv (subst theta ty1) (subst theta ty2))

\end{verbatim}
After performing a unification, the resulting substitution is applied
to the current context and the resulting context is subject to a
context reduction. This context reduction retains all predicates whose
types are simple variables and for all other types checks whether an
instance exists. A minor complication arises due to constrained types,
which at present are used to implement overloading of guard
expressions and of numeric literals in patterns. The set of admissible
types of a constrained type may be restricted by the current context
after the context reduction and thus may cause a further extension of
the current substitution.
\begin{verbatim}

> reduceContext :: Position -> String -> Doc -> TCEnv -> Context -> a
>               -> TcState (Context,a)
> reduceContext p what doc tcEnv cx x =
>   do
>     iEnv <- liftSt (liftSt envRt)
>     theta <- liftSt fetchSt
>     let (cx1,cx2) = partitionContext (reduceTypePreds iEnv (subst theta cx))
>     theta' <- foldM (reportMissingInstance p what doc tcEnv iEnv) idSubst cx2
>     liftSt (updateSt_ (compose theta'))
>     return (cx1,x)

> reduceTypePreds :: InstEnv -> Context -> Context
> reduceTypePreds iEnv = concatMap (reduceTypePred iEnv)

> reduceTypePred :: InstEnv -> TypePred -> Context
> reduceTypePred iEnv (TypePred cls ty) =
>   maybe [TypePred cls ty] (reduceTypePreds iEnv) (instContext iEnv cls ty)

> instContext :: InstEnv -> QualIdent -> Type -> Maybe Context
> instContext iEnv cls (TypeConstructor tc tys) =
>   fmap (map (expandAliasType tys)) (lookupEnv (CT cls tc) iEnv)
> instContext _ _ (TypeVariable _) = Nothing
> instContext _ _ (TypeConstrained _ _) = Nothing
> instContext iEnv cls (TypeArrow ty1 ty2) =
>   fmap (map (expandAliasType [ty1,ty2])) (lookupEnv (CT cls qArrowId) iEnv)
> instContext _ _ (TypeSkolem _) = Nothing

> partitionContext :: Context -> (Context,Context)
> partitionContext cx = partition (\(TypePred _ ty) -> isTypeVar ty) (nub cx)
>   where isTypeVar (TypeConstructor _ _) = False
>         isTypeVar (TypeVariable _) = True
>         isTypeVar (TypeConstrained _ _) = False
>         isTypeVar (TypeArrow _ _) = False
>         isTypeVar (TypeSkolem _) = False

> reportMissingInstance :: Position -> String -> Doc -> TCEnv -> InstEnv
>                       -> TypeSubst -> TypePred -> TcState TypeSubst
> reportMissingInstance p what doc tcEnv iEnv theta (TypePred cls ty) =
>   case subst theta ty of
>     TypeConstrained tys tv ->
>       case filter (hasInstance iEnv cls) tys of
>         [] ->
>           errorAt p (noInstance what doc tcEnv cls (TypeConstrained tys tv))
>         [ty'] -> return (bindSubst tv ty' theta)
>         _ -> return theta
>     ty'
>       | hasInstance iEnv cls ty' -> return theta
>       | otherwise -> errorAt p (noInstance what doc tcEnv cls ty')

> hasInstance :: InstEnv -> QualIdent -> Type -> Bool
> hasInstance iEnv cls ty = isJust (instContext iEnv cls ty)

\end{verbatim}
When a constrained type variable that is not free in the type
environment disappears from the current type, the type becomes
ambiguous. For instance, the type of the expression
\begin{verbatim}
  let x = read "" in show x
\end{verbatim}
is ambiguous assuming that \texttt{read} and \texttt{show} have types
\begin{verbatim}
  read :: Read a => String -> a
  show :: Show a => a -> String
\end{verbatim}
because the compiler cannot determine which \texttt{Read} and
\texttt{Show} instances to use.

In the case of expressions with an ambiguous numeric type, i.e., a
type that must be an instance of the \texttt{Num} class, the compiler
tries to resolve the ambiguity by choosing the first type from the set
$\left\{ \texttt{Int}, \texttt{Float} \right\}$ that satisfies all
constraints for the ambiguous type variable. An error is reported if
no such type exists.

This is similar to Haskell's default rules, except that the user can
specify the set of types used for resolving ambiguous numeric types
with a default declaration. Furthermore, Haskell resolves ambiguous
types only if all classes involved are defined in the Haskell Prelude
or a standard library (cf.\ Sect.~4.3.4 of the revised Haskell'98
report~\cite{PeytonJones03:Haskell}).

\ToDo{Support default declarations.}
\begin{verbatim}

> applyDefaults :: Position -> String -> Doc -> TCEnv -> Set Int -> Context
>               -> Type -> TcState Context
> applyDefaults p what doc tcEnv fvs cx ty =
>   do
>     iEnv <- liftSt (liftSt envRt)
>     let theta = foldr (bindDefault iEnv) idSubst tpss
>         lcx' = fst (partitionContext (subst theta lcx))
>         ty' = subst theta ty
>     unless (null lcx')
>            (errorAt p (ambiguousType what doc tcEnv lcx' (QualType gcx ty')))
>     liftSt (updateSt_ (compose theta))
>     return gcx
>   where (gcx,lcx) = splitContext fvs cx
>         tpss = groupBy sameType (sort lcx)
>         sameType (TypePred _ ty1) (TypePred _ ty2) = ty1 == ty2

> bindDefault :: InstEnv -> [TypePred] -> TypeSubst -> TypeSubst
> bindDefault iEnv tps =
>   case defaultType iEnv tps of
>     Just ty -> bindSubst (head [tv | TypePred _ (TypeVariable tv) <- tps]) ty
>     Nothing -> id

> defaultType :: InstEnv -> [TypePred] -> Maybe Type
> defaultType iEnv tps =
>   case [ty | ty <- defaultTypes, all (flip (hasInstance iEnv) ty) clss] of
>     [] -> Nothing
>     ty:_ -> Just ty
>   where clss = [cls | TypePred cls _ <- tps]
>         defaultTypes
>           | qNumId `elem` clss = numTypes
>           | qFractionalId `elem` clss = fracTypes
>           | otherwise = []

\end{verbatim}
The function \texttt{splitContext} splits a context
$\overline{C_n\,\alpha_n}$ into a pair of contexts
$(\overline{C_{n_1}\alpha_{n_1}}, \overline{C_{n_2}\alpha_{n_2}})$
such that all type variables $\overline{\alpha_{n_1}}$ are elements of
a given set of type variables.
\begin{verbatim}

> splitContext :: Set Int -> Context -> (Context,Context)
> splitContext fvs =
>   partition (\(TypePred _ (TypeVariable tv)) -> tv `elemSet` fvs)

\end{verbatim}
For each function declaration, the type checker ensures that no skolem
type escapes its scope. This is slightly more general than the
algorithm in~\cite{LauferOdersky94:AbstractTypes}, which checks for
escaping skolems at every let binding, but is still sound.
\begin{verbatim}

> checkSkolems :: Position -> TCEnv -> Doc -> Set Int -> Type -> TcState ()
> checkSkolems p tcEnv what fs ty =
>   do
>     ty' <- liftM (flip subst ty) (liftSt fetchSt)
>     unless (all (`elemSet` fs) (typeSkolems ty'))
>            (errorAt p (skolemEscapingScope tcEnv what ty'))

\end{verbatim}
\paragraph{Instantiation and Generalization}
We use negative offsets for fresh type variables.
\begin{verbatim}

> fresh :: (Int -> a) -> TcState a
> fresh f = liftM f (liftSt (liftSt (liftRt (updateSt (1 +)))))

> freshVar :: (Int -> a) -> TcState a
> freshVar f = fresh (\n -> f (- n))

> freshTypeVar :: TcState Type
> freshTypeVar = freshVar TypeVariable

> freshQualType :: [QualIdent] -> TcState (Context,Type)
> freshQualType clss =
>   do
>     tv <- freshTypeVar
>     return ([TypePred cls tv | cls <- clss],tv)

> freshEnumType, freshNumType, freshFracType :: TcState (Context,Type)
> freshEnumType = freshQualType [qEnumId]
> freshNumType = freshQualType numClasses
> freshFracType = freshQualType fracClasses

> freshConstrained :: [Type] -> TcState Type
> freshConstrained tys = freshVar (TypeConstrained tys)

> freshSkolem :: TcState Type
> freshSkolem = fresh TypeSkolem

> inst :: TypeScheme -> TcState (Context,Type)
> inst (ForAll n (QualType cx ty)) =
>   do
>     tys <- replicateM n freshTypeVar
>     return (map (expandAliasType tys) cx,expandAliasType tys ty)

\end{verbatim}
The functions \texttt{numClasses} and \texttt{fracClasses} return
lists of class and super class identifiers for the classes
\texttt{Num} and \texttt{Fractional}, respectively. These are used in
order to compute the contexts of overloaded integral and fractional
literals. In principle, the compiler should determine these lists from
the type constructor environment. However, it may be unable to do so
because the identifiers \texttt{Num} and \texttt{Fractional} may be
not in scope or ambiguous.

\ToDo{Keep these lists in sync with the \texttt{Prelude} and make sure
  that they are sorted properly.}
\begin{verbatim}

> numClasses, fracClasses :: [QualIdent]
> numClasses = [qEqId,qNumId,qShowId]
> fracClasses = [qEqId,qFractionalId,qNumId,qShowId]

\end{verbatim}
The function \texttt{skol} instantiates the type of data and newtype
constructors in patterns. All universally quantified type variables
are instantiated with fresh type variables and all existentially
quantified type variables are instantiated with fresh skolem types.
Note that the context of a constructor's type can only constrain the
universally quantified type variables.
\begin{verbatim}

> skol :: TypeScheme -> TcState (Context,Type)
> skol (ForAll n (QualType cx ty)) =
>   do
>     tys <- replicateM m freshTypeVar
>     tys' <- replicateM (n - m) freshSkolem
>     return (map (expandAliasType tys) cx,expandAliasType (tys ++ tys') ty)
>   where m = arity (arrowBase ty)
>         arity (TypeConstructor _ tys) = length tys

\end{verbatim}
The function \texttt{gen} generalizes a context \emph{cx} and a type
$\tau$ into a type scheme $\forall\overline{\alpha} . \emph{cx}
\Rightarrow \tau$ by universally quantifying all type variables that
are free in $\tau$ and not fixed by the environment. The set of the
latter is given by \texttt{gen}'s first argument.
\begin{verbatim}

> gen :: Set Int -> Context -> Type -> TypeScheme
> gen fvs cx ty = ForAll (length tvs) (subst theta (QualType cx ty))
>   where tvs = [tv | tv <- nub (typeVars ty), tv `notElemSet` fvs]
>         theta = foldr2 bindSubst idSubst tvs (map TypeVariable [0..])

> replicateM :: Monad m => Int -> m a -> m [a]
> replicateM n = sequence . replicate n

\end{verbatim}
\paragraph{Auxiliary Functions}
The functions \texttt{fvEnv} and \texttt{fsEnv} compute the set of
free type variables and free skolems of a type environment,
respectively. We ignore the types of data and newtype constructors
here because we know that they are closed.
\begin{verbatim}

> fvEnv :: ValueEnv -> Set Int
> fvEnv tyEnv = fromListSet (concatMap typeVars (localTypes tyEnv))

> fsEnv :: ValueEnv -> Set Int
> fsEnv tyEnv = fromListSet (concatMap typeSkolems (localTypes tyEnv))

> localTypes :: ValueEnv -> [TypeScheme]
> localTypes tyEnv = [ty | (_,Value _ ty) <- localBindings tyEnv]

\end{verbatim}
The function \texttt{untyped} is used when transforming annotated
syntax tree nodes into typed syntax tree nodes without adding type
information. This is useful for nodes which contain no attributes
themselves, e.g., operator fixity declarations.
\begin{verbatim}

> untyped :: Functor f => f a -> f Type
> untyped = fmap (internalError "untyped")

\end{verbatim}
Error functions.
\begin{verbatim}

> polymorphicVar :: Ident -> String
> polymorphicVar v = "Variable " ++ name v ++ " cannot have polymorphic type"

> typeSigTooGeneral :: TCEnv -> Doc -> QualTypeExpr -> TypeScheme -> String
> typeSigTooGeneral tcEnv what ty sigma = show $
>   vcat [text "Type signature too general", what,
>         text "Inferred type:" <+> ppTypeScheme tcEnv sigma,
>         text "Type signature:" <+> ppQualTypeExpr ty]

> methodSigTooGeneral :: TCEnv -> Doc -> TypeScheme -> TypeScheme -> String
> methodSigTooGeneral tcEnv what ty sigma = show $
>   vcat [text "Method type not general enough", what,
>         text "Inferred type:" <+> ppTypeScheme tcEnv sigma,
>         text "Expected type:" <+> ppTypeScheme tcEnv ty]

> wrongArity :: QualIdent -> Int -> Int -> String
> wrongArity c arity argc = show $
>   hsep [text "Constructor", ppQIdent c, text "requires",
>         int arity, text (plural arity "argument"),
>         text "in patterns, but is applied to", int argc]
>   where plural n x = if n == 1 then x else x ++ "s"

> nonFunctionType :: String -> Doc -> TCEnv -> Type -> String
> nonFunctionType what doc tcEnv ty = show $
>   vcat [text "Type error in" <+> text what, doc,
>         text "Type:" <+> ppType tcEnv ty,
>         text "Cannot be applied"]

> nonBinaryOp :: String -> Doc -> TCEnv -> Type -> String
> nonBinaryOp what doc tcEnv ty = show $
>   vcat [text "Type error in" <+> text what, doc,
>         text "Type:" <+> ppType tcEnv ty,
>         text "Cannot be used as binary operator"]

> typeMismatch :: String -> Doc -> TCEnv -> Type -> Type -> Doc -> String
> typeMismatch what doc tcEnv ty1 ty2 reason = show $
>   vcat [text "Type error in" <+> text what, doc,
>         text "Inferred type:" <+> ppType tcEnv ty2,
>         text "Expected type:" <+> ppType tcEnv ty1,
>         reason]

> skolemEscapingScope :: TCEnv -> Doc -> Type -> String
> skolemEscapingScope tcEnv what ty = show $
>   vcat [text "Existential type escapes out of its scope", what,
>         text "Type:" <+> ppType tcEnv ty]

> invalidCType :: String -> TCEnv -> Type -> String
> invalidCType what tcEnv ty = show $
>   vcat [text ("Invalid " ++ what ++ " type in foreign declaration:"),
>         ppType tcEnv ty]

> recursiveType :: TCEnv -> Int -> Type -> Doc
> recursiveType tcEnv tv ty = incompatibleTypes tcEnv (TypeVariable tv) ty

> incompatibleTypes :: TCEnv -> Type -> Type -> Doc
> incompatibleTypes tcEnv ty1 ty2 =
>   sep [text "Types" <+> ppType tcEnv ty1,
>        nest 2 (text "and" <+> ppType tcEnv ty2),
>        text "are incompatible"]

> ambiguousType :: String -> Doc -> TCEnv -> Context -> QualType -> String
> ambiguousType what doc tcEnv cx' (QualType cx ty) = show $
>   vcat [text "Ambiguous type variable" <> plural tvs <+>
>           list (map (ppType tcEnv) tvs) <+> text "in type",
>         ppQualType tcEnv (canonType (QualType (cx' ++ cx) ty)),
>         text "inferred for" <+> text what, doc]
>   where tvs = nub [ty | TypePred _ ty <- cx']
>         plural (_:xs) = if null xs then empty else char 's'
>         list [x] = x
>         list [x1,x2] = x1 <+> text "and" <+> x2
>         list xs = hsep (map (<> comma) (init xs)) <+> text "and" <+> last xs

> noInstance :: String -> Doc -> TCEnv -> QualIdent -> Type -> String
> noInstance what doc tcEnv cls ty = show $
>   vcat [sep [text "Missing instance for",
>              ppQIdent cls' <+> ppTypeExpr 2 ty',
>              text "in" <+> text what],
>         doc]
>   where QualTypeExpr [ClassAssert cls' _] ty' =
>           fromQualType tcEnv (QualType [TypePred cls (TypeVariable 0)] ty)

\end{verbatim}
