% -*- LaTeX -*-
% $Id: TypeCheck.lhs 1981 2006-10-23 22:42:43Z wlux $
%
% Copyright (c) 1999-2006, Wolfgang Lux
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

> typeCheck :: ModuleIdent -> TCEnv -> InstEnv -> ValueEnv -> [TopDecl]
>           -> Error ValueEnv
> typeCheck m tcEnv iEnv tyEnv ds =
>   run (tcDecls m tcEnv [d | BlockDecl d <- vds] >>= \cx ->
>        unless (null cx) (internalError ("typeCheck " ++ show cx)) >>
>        liftSt fetchSt >>= \theta -> liftM (subst theta) fetchSt)
>       iEnv
>       (foldr (bindConstrs m tcEnv) tyEnv tds)
>   where (tds,vds) = partition isTypeDecl ds

\end{verbatim}
Type checking of a goal is simpler because there are no type
declarations.
\begin{verbatim}

> typeCheckGoal :: TCEnv -> InstEnv -> ValueEnv -> Goal -> Error ValueEnv
> typeCheckGoal tcEnv iEnv tyEnv g =
>    run (tcGoal emptyMIdent tcEnv g >>
>         liftSt fetchSt >>= \theta -> liftM (subst theta) fetchSt)
>        iEnv
>        tyEnv

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
\paragraph{Defining Data Constructors}
First, the types of all data and newtype constructors are entered into
the type environment. All type synonyms occurring in their types are
expanded. We cannot use \texttt{expandPolyType} for expanding the type
of a data or newtype constructor in function \texttt{bindConstr}
because of the different normalization scheme used for constructor
types and also because the name of the type could be ambiguous.
\begin{verbatim}

> bindConstrs :: ModuleIdent -> TCEnv -> TopDecl -> ValueEnv -> ValueEnv
> bindConstrs m tcEnv (DataDecl _ tc tvs cs) tyEnv = foldr bind tyEnv cs
>   where ty0 = constrType m tc tvs
>         bind (ConstrDecl _ _ c tys) =
>           bindConstr DataConstructor m tcEnv tvs c tys ty0
>         bind (ConOpDecl _ _ ty1 op ty2) =
>           bindConstr DataConstructor m tcEnv tvs op [ty1,ty2] ty0
> bindConstrs m tcEnv (NewtypeDecl _ tc tvs nc) tyEnv = bind nc tyEnv
>   where ty0 = constrType m tc tvs
>         bind (NewConstrDecl _ c ty) =
>           bindConstr NewtypeConstructor m tcEnv tvs c [ty] ty0
> bindConstrs _ _ (TypeDecl _ _ _ _) tyEnv = tyEnv
> bindConstrs _ _ (ClassDecl _ _ _) tyEnv = tyEnv
> bindConstrs _ _ (InstanceDecl _ _ _) tyEnv = tyEnv
> bindConstrs _ _ (BlockDecl _) tyEnv = tyEnv

> bindConstr :: (QualIdent -> TypeScheme -> ValueInfo) -> ModuleIdent
>            -> TCEnv -> [Ident] -> Ident -> [TypeExpr] -> Type
>            -> ValueEnv -> ValueEnv
> bindConstr f m tcEnv tvs c tys ty0 =
>   globalBindTopEnv m c (f (qualifyWith m c) ty')
>   where ty' = typeScheme $ normalize (length tvs) $
>               qualType (foldr TypeArrow ty0 (expandMonoTypes tcEnv tvs tys))

> constrType :: ModuleIdent -> Ident -> [Ident] -> Type
> constrType m tc tvs =
>   TypeConstructor (qualifyWith m tc) (map TypeVariable [0..length tvs-1])

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

> bindTypeSigs :: Decl -> SigEnv -> SigEnv
> bindTypeSigs (TypeSig _ vs ty) env = foldr (flip bindEnv ty) env vs 
> bindTypeSigs _ env = env
        
\end{verbatim}
\paragraph{Type Inference}
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

Note that \texttt{tcDeclRhs} ignores the context present in a
function's type signature. This prevents spurious missing instance
errors when the inferred type of a function is less general than the
declared type. For instance, if the type signature's context were
merged with the inferred context, the compiler would report a missing
instance \texttt{Prelude.Eq (a -> a)} for the declaration
\begin{verbatim}
  f :: Eq a => a
  f = id
\end{verbatim}
instead of reporting that the inferred type \texttt{a -> a} is less
general than the type signature.
\begin{verbatim}

> tcDecls :: ModuleIdent -> TCEnv -> [Decl] -> TcState Context
> tcDecls m tcEnv ds =
>   foldM (tcDeclGroup m tcEnv (foldr bindTypeSigs noSigs ods)) []
>         (scc bv (qfv m) vds)
>   where (vds,ods) = partition isValueDecl ds

> tcDeclGroup :: ModuleIdent -> TCEnv -> SigEnv -> Context -> [Decl]
>             -> TcState Context
> tcDeclGroup m tcEnv _ cx [ForeignDecl p cc ie f ty] =
>   do
>     tcForeignFunct m tcEnv p cc ie f ty
>     return cx
> tcDeclGroup m tcEnv sigs cx [FreeDecl p vs] =
>   do
>     mapM_ (tcVariable m tcEnv sigs False p) vs
>     return cx
> tcDeclGroup m tcEnv sigs cx ds =
>   do
>     tyEnv0 <- fetchSt
>     tys <- mapM (tcDeclLhs m tcEnv sigs) ds
>     cx' <- foldM (uncurry . tcDeclRhs m tcEnv) cx (zip tys ds)
>     tyEnv <- fetchSt
>     theta <- liftSt fetchSt
>     let tvss = map (typeVars . subst theta . flip varType tyEnv) vs
>         fvs = foldr addToSet (fvEnv (subst theta tyEnv0)) (concat tvss)
>         (gcx,lcx) = splitContext fvs cx'
>     zipWithM_ (genDecl m tcEnv sigs . gen fvs lcx . subst theta . snd) tys ds
>     return gcx
>   where vs = [v | PatternDecl _ t _ <- ds, v <- bv t]

> tcDeclLhs :: ModuleIdent -> TCEnv -> SigEnv -> Decl -> TcState (Context,Type)
> tcDeclLhs m tcEnv sigs (FunctionDecl p f _) = tcVariable m tcEnv sigs True p f
> tcDeclLhs m tcEnv sigs (PatternDecl p t _) = tcConstrTerm m tcEnv sigs p t

> tcDeclRhs :: ModuleIdent -> TCEnv -> Context -> (Context,Type) -> Decl
>           -> TcState Context
> tcDeclRhs m tcEnv cx (_,tyLhs) d@(FunctionDecl p f eqs) =
>   do
>     tyEnv0 <- fetchSt
>     theta <- liftSt fetchSt
>     cxs <- mapM (tcEquation m tcEnv (fsEnv (subst theta tyEnv0)) tyLhs) eqs
>     reduceContext p "function declaration" (ppDecl d) m (cx ++ concat cxs)
> tcDeclRhs m tcEnv cx (cxLhs,tyLhs) d@(PatternDecl p t rhs) =
>   do
>     tyEnv0 <- fetchSt
>     tcRhs m tcEnv rhs >>=
>       unifyDecl p "pattern declaration" (ppDecl d) m tyEnv0 (cx++cxLhs) tyLhs

> tcEquation :: ModuleIdent -> TCEnv -> Set Int -> Type -> Equation
>            -> TcState Context
> tcEquation m tcEnv fs ty eq@(Equation p lhs rhs) =
>   do
>     tyEnv0 <- fetchSt
>     cx <-
>       tcEqn m tcEnv p ts rhs >>=
>       unifyDecl p "function declaration" (ppEquation eq) m tyEnv0 [] ty
>     checkSkolems p m (text "Function:" <+> ppIdent f) fs ty
>     return cx
>   where (f,ts) = flatLhs lhs

> tcEqn :: ModuleIdent -> TCEnv -> Position -> [ConstrTerm] -> Rhs
>       -> TcState (Context,Type)
> tcEqn m tcEnv p ts rhs =
>   do
>     (cxs,tys) <- liftM unzip $ mapM (tcConstrTerm m tcEnv noSigs p) ts
>     (cx,ty) <- tcRhs m tcEnv rhs
>     return (concat cxs ++ cx,foldr TypeArrow ty tys)

> tcGoal :: ModuleIdent -> TCEnv -> Goal -> TcState ()
> tcGoal m tcEnv (Goal p e ds) =
>   do
>     tyEnv0 <- fetchSt
>     alpha <- freshTypeVar
>     tcRhs m tcEnv (SimpleRhs p e ds) >>=
>       unifyDecl p "goal" (ppExpr 0 e) m tyEnv0 [] alpha
>     checkSkolems p emptyMIdent (text "Goal:" <+> ppExpr 0 e) zeroSet alpha

> unifyDecl :: Position -> String -> Doc -> ModuleIdent -> ValueEnv
>           -> Context -> Type -> (Context,Type) -> TcState Context
> unifyDecl p what doc m tyEnv0 cxLhs tyLhs (cxRhs,tyRhs) =
>   do
>     cx <- unify p what doc m tyLhs (cxLhs ++ cxRhs,tyRhs)
>     theta <- liftSt fetchSt
>     let ty = subst theta tyLhs
>         fvs = foldr addToSet (fvEnv (subst theta tyEnv0)) (typeVars ty)
>         tvs = [ty | TypePred _ ty <- snd (splitContext fvs cx)]
>     unless (null tvs) (errorAt p (ambiguousType what doc m (nub tvs) cx ty))
>     return cx

\end{verbatim}
The code in \texttt{genDecl} below verifies that the inferred type for
a function matches its declared type. Since the type inferred for the
left hand side of a function or variable declaration is an instance of
its declared type -- provided a type signature is given -- it can only
be more specific. Therefore, if the inferred type does not match the
type signature the declared type must be too general. Note that it is
possible that the inferred context is only a subset of the declared
context because the left hand side context of a function declaration
is (deliberately) ignored in \texttt{tcDeclRhs} above. No check is
necessary for the variables in variable and other pattern declarations
because the types of variables must be monomorphic, which is checked
in \texttt{tcVariable} below.
\begin{verbatim}

> genDecl :: ModuleIdent -> TCEnv -> SigEnv -> TypeScheme -> Decl -> TcState ()
> genDecl m tcEnv sigs sigma (FunctionDecl p f _) =
>   case lookupEnv f sigs of
>     Just sigTy
>       | sigma `matchesTypeSig` expandPolyType tcEnv sigTy -> return ()
>       | otherwise -> errorAt p (typeSigTooGeneral m what sigTy sigma)
>     Nothing -> updateSt_ (rebindFun m f sigma)
>   where what = text "Function:" <+> ppIdent f
> genDecl _ _ _ _ (PatternDecl _ _ _) = return ()

> matchesTypeSig :: TypeScheme -> TypeScheme -> Bool
> ForAll _ (QualType cx ty) `matchesTypeSig` ForAll _ (QualType sigCx sigTy) =
>   ty == sigTy && all (`elem` sigCx) cx

\end{verbatim}
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
>           | ie == Just "dynamic" = checkCDynCallType m p ty
>           | maybe False ('&' `elem`) ie = checkCAddrType m p ty
>           | otherwise = checkCCallType m p ty

> checkCCallType :: ModuleIdent -> Position -> Type -> TcState ()
> checkCCallType m p (TypeArrow ty1 ty2)
>   | isCArgType ty1 = checkCCallType m p ty2
>   | otherwise = errorAt p (invalidCType "argument" m ty1)
> checkCCallType m p ty
>   | isCRetType ty = return ()
>   | otherwise = errorAt p (invalidCType "result" m ty)

> checkCDynCallType :: ModuleIdent -> Position -> Type -> TcState ()
> checkCDynCallType m p (TypeArrow (TypeConstructor tc [ty1]) ty2)
>   | tc == qFunPtrId && ty1 == ty2 = checkCCallType m p ty1
> checkCDynCallType m p ty = errorAt p (invalidCType "dynamic function" m ty)

> checkCAddrType :: ModuleIdent -> Position -> Type -> TcState ()
> checkCAddrType m p ty
>   | isCPtrType ty = return ()
>   | otherwise = errorAt p (invalidCType "static address" m ty)

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

> litType :: Literal -> (Context,Type)
> litType (Char _) = ([],charType)
> litType (Int _) = ([],intType)
> litType (Float _) = ([],floatType)
> litType (String _) = ([],stringType)

> tcVariable :: ModuleIdent -> TCEnv -> SigEnv -> Bool -> Position
>            -> Ident -> TcState (Context,Type)
> tcVariable m tcEnv sigs poly p v =
>   case lookupEnv v sigs of
>     Just ty -> sigType m poly p v (expandPolyType tcEnv ty)
>     Nothing -> freshType m v
>   where sigType m poly p v ty
>           | poly || isMonoType ty = updateSt_ (bindFun m v ty) >> inst ty
>           | otherwise = errorAt p (polymorphicVar v)
>         freshType m v =
>           do
>             ty <- freshTypeVar
>             updateSt_ (bindFun m v (monoType ty))
>             return ([],ty)
>         isMonoType (ForAll n _) = n == 0

> tcConstrTerm :: ModuleIdent -> TCEnv -> SigEnv -> Position -> ConstrTerm
>              -> TcState (Context,Type)
> tcConstrTerm m _ _ _ (LiteralPattern l) = return (litType l)
> tcConstrTerm m _ _ _ (NegativePattern l) = return (litType l)
> tcConstrTerm m tcEnv sigs p (VariablePattern v) =
>   tcVariable m tcEnv sigs False p v
> tcConstrTerm m tcEnv sigs p t@(ConstructorPattern c ts) =
>   tcConstrApp m tcEnv sigs p (ppConstrTerm 0 t) c ts
> tcConstrTerm m tcEnv sigs p t@(InfixPattern t1 op t2) =
>   tcConstrApp m tcEnv sigs p (ppConstrTerm 0 t) op [t1,t2]
> tcConstrTerm m tcEnv sigs p (ParenPattern t) = tcConstrTerm m tcEnv sigs p t
> tcConstrTerm m tcEnv sigs p (TuplePattern ts) =
>   do
>     (cxs,tys) <- liftM unzip $ mapM (tcConstrTerm m tcEnv sigs p) ts
>     return (concat cxs,tupleType tys)
> tcConstrTerm m tcEnv sigs p t@(ListPattern ts) =
>   do
>     ty <- freshTypeVar
>     cxs <- mapM (tcElem (ppConstrTerm 0 t) ty) ts
>     return (concat cxs,listType ty)
>   where tcElem doc ty t =
>           tcConstrTerm m tcEnv sigs p t >>=
>           unify p "pattern" (doc $-$ text "Term:" <+> ppConstrTerm 0 t) m ty
> tcConstrTerm m tcEnv sigs p t@(AsPattern v t') =
>   do
>     (cx,ty) <- tcConstrTerm m tcEnv sigs p (VariablePattern v)
>     cx' <-
>       tcConstrTerm m tcEnv sigs p t' >>=
>       unify p "pattern" (ppConstrTerm 0 t) m ty
>     return (cx ++ cx',ty)
> tcConstrTerm m tcEnv sigs p (LazyPattern t) = tcConstrTerm m tcEnv sigs p t

> tcConstrApp :: ModuleIdent -> TCEnv -> SigEnv -> Position -> Doc
>             -> QualIdent -> [ConstrTerm] -> TcState (Context,Type)
> tcConstrApp m tcEnv sigs p doc c ts =
>   do
>     tyEnv <- fetchSt
>     (cx,(tys,ty)) <- liftM (apSnd arrowUnapply) (skol (conType c tyEnv))
>     unless (length tys == n) (errorAt p (wrongArity c (length tys) n))
>     cxs <- zipWithM (tcConstrArg m tcEnv sigs p doc) ts tys
>     return (cx ++ concat cxs,ty)
>   where n = length ts

> tcConstrArg :: ModuleIdent -> TCEnv -> SigEnv -> Position -> Doc
>             -> ConstrTerm -> Type -> TcState Context
> tcConstrArg m tcEnv sigs p doc t ty =
>   tcConstrTerm m tcEnv sigs p t >>=
>   unify p "pattern" (doc $-$ text "Term:" <+> ppConstrTerm 0 t) m ty

> tcRhs :: ModuleIdent -> TCEnv -> Rhs -> TcState (Context,Type)
> tcRhs m tcEnv (SimpleRhs p e ds) =
>   do
>     cx <- tcDecls m tcEnv ds
>     (cx',ty) <- tcExpr m tcEnv p e
>     return (cx ++ cx',ty)
> tcRhs m tcEnv (GuardedRhs es ds) =
>   do
>     cx <- tcDecls m tcEnv ds
>     gty <- guardType es
>     ty <- freshTypeVar
>     cxs <- mapM (tcCondExpr m tcEnv gty ty) es
>     return (cx ++ concat cxs,ty)
>   where guardType es
>           | length es > 1 = return boolType
>           | otherwise = freshGuard

> tcCondExpr :: ModuleIdent -> TCEnv -> Type -> Type -> CondExpr
>            -> TcState Context
> tcCondExpr m tcEnv gty ty (CondExpr p g e) =
>   do
>     cx <- tcExpr m tcEnv p g >>= unify p "guard" (ppExpr 0 g) m gty
>     cx' <-
>       tcExpr m tcEnv p e >>= unify p "guarded expression" (ppExpr 0 e) m ty
>     return (cx ++ cx')

> tcExpr :: ModuleIdent -> TCEnv -> Position -> Expression
>        -> TcState (Context,Type)
> tcExpr _ _ _ (Literal l) = return (litType l)
> tcExpr m tcEnv p (Variable v) = fetchSt >>= inst . funType v
> tcExpr m tcEnv p (Constructor c) = fetchSt >>= inst . conType c
> tcExpr m tcEnv p (Typed e sig) =
>   do
>     tyEnv0 <- fetchSt
>     (cx,ty) <- inst sigma'
>     cx' <-
>       tcExpr m tcEnv p e >>=
>       unifyDecl p "explicitly typed expression" (ppExpr 0 e) m tyEnv0 [] ty
>     theta <- liftSt fetchSt
>     let fvs = fvEnv (subst theta tyEnv0)
>         sigma = gen fvs (snd (splitContext fvs cx')) (subst theta ty)
>     unless (sigma `matchesTypeSig` sigma')
>       (errorAt p (typeSigTooGeneral m (text "Expression:" <+> ppExpr 0 e)
>                                     sig sigma))
>     return (cx ++ cx',ty)
>   where sigma' = expandPolyType tcEnv sig
> tcExpr m tcEnv p (Paren e) = tcExpr m tcEnv p e
> tcExpr m tcEnv p (Tuple es) =
>   do
>     (cxs,tys) <- liftM unzip $ mapM (tcExpr m tcEnv p) es
>     return (concat cxs,tupleType tys)
> tcExpr m tcEnv p e@(List es) =
>   do
>     ty <- freshTypeVar
>     cxs <- mapM (tcElem (ppExpr 0 e) ty) es
>     return (concat cxs,listType ty)
>   where tcElem doc ty e =
>           tcExpr m tcEnv p e >>=
>           unify p "expression" (doc $-$ text "Term:" <+> ppExpr 0 e) m ty
> tcExpr m tcEnv p (ListCompr e qs) =
>   do
>     cxs <- mapM (tcQual m tcEnv p) qs
>     (cx,ty) <- tcExpr m tcEnv p e
>     return (concat cxs ++ cx,listType ty)
> tcExpr m tcEnv p e@(EnumFrom e1) =
>   do
>     cx <-
>       tcExpr m tcEnv p e1 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) m intType
>     return (cx,listType intType)
> tcExpr m tcEnv p e@(EnumFromThen e1 e2) =
>   do
>     cx <-
>       tcExpr m tcEnv p e1 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) m intType
>     cx' <-
>       tcExpr m tcEnv p e2 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) m intType
>     return (cx ++ cx',listType intType)
> tcExpr m tcEnv p e@(EnumFromTo e1 e2) =
>   do
>     cx <-
>       tcExpr m tcEnv p e1 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) m intType
>     cx' <-
>       tcExpr m tcEnv p e2 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) m intType
>     return (cx ++ cx',listType intType)
> tcExpr m tcEnv p e@(EnumFromThenTo e1 e2 e3) =
>   do
>     cx <-
>       tcExpr m tcEnv p e1 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) m intType
>     cx' <-
>       tcExpr m tcEnv p e2 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) m intType
>     cx'' <-
>       tcExpr m tcEnv p e3 >>=
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e3) m intType
>     return (cx ++ cx' ++ cx'',listType intType)
> tcExpr m tcEnv p e@(UnaryMinus op e1) =
>   do
>     cx <-
>       tcExpr m tcEnv p e1 >>=
>       unify p "unary negation" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             m ty
>     return (cx,ty)
>   where ty
>           | op == minusId = intType
>           | op == fminusId = floatType
>           | otherwise = internalError ("tcExpr unary " ++ name op)
> tcExpr m tcEnv p e@(Apply e1 e2) =
>   do
>     (cx,alpha,beta) <-
>       tcExpr m tcEnv p e1 >>=
>       tcArrow p "application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) m
>     cx' <-
>       tcExpr m tcEnv p e2 >>=
>       unify p "application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2)
>             m alpha
>     return (cx ++ cx',beta)
> tcExpr m tcEnv p e@(InfixApply e1 op e2) =
>   do
>     (cx,alpha,beta,gamma) <-
>       tcExpr m tcEnv p (infixOp op) >>=
>       tcBinary p "infix application"
>                (ppExpr 0 e $-$ text "Operator:" <+> ppOp op) m
>     cx' <-
>       tcExpr m tcEnv p e1 >>=
>       unify p "infix application"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) m alpha
>     cx'' <-
>       tcExpr m tcEnv p e2 >>=
>       unify p "infix application"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) m beta
>     return (cx ++ cx' ++ cx'',gamma)
> tcExpr m tcEnv p e@(LeftSection e1 op) =
>   do
>     (cx,alpha,beta) <-
>       tcExpr m tcEnv p (infixOp op) >>=
>       tcArrow p "left section" (ppExpr 0 e $-$ text "Operator:" <+> ppOp op) m
>     cx' <-
>       tcExpr m tcEnv p e1 >>=
>       unify p "left section" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             m alpha
>     return (cx ++ cx',beta)
> tcExpr m tcEnv p e@(RightSection op e1) =
>   do
>     (cx,alpha,beta,gamma) <-
>       tcExpr m tcEnv p (infixOp op) >>=
>       tcBinary p "right section"
>                (ppExpr 0 e $-$ text "Operator:" <+> ppOp op) m
>     cx' <-
>       tcExpr m tcEnv p e1 >>=
>       unify p "right section" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             m beta
>     return (cx ++ cx',TypeArrow alpha gamma)
> tcExpr m tcEnv p (Lambda ts e) =
>   do
>     (cxs,tys) <- liftM unzip $ mapM (tcConstrTerm m tcEnv noSigs p) ts
>     (cx',ty) <- tcExpr m tcEnv p e
>     return (concat cxs ++ cx',foldr TypeArrow ty tys)
> tcExpr m tcEnv p (Let ds e) =
>   do
>     cx <- tcDecls m tcEnv ds
>     (cx',ty) <- tcExpr m tcEnv p e
>     return (cx ++ cx',ty)
> tcExpr m tcEnv p (Do sts e) =
>   do
>     cxs <- mapM (tcStmt m tcEnv p) sts
>     ty <- liftM ioType freshTypeVar
>     cx <- tcExpr m tcEnv p e >>= unify p "statement" (ppExpr 0 e) m ty
>     return (concat cxs ++ cx,ty)
> tcExpr m tcEnv p e@(IfThenElse e1 e2 e3) =
>   do
>     cx <-
>       tcExpr m tcEnv p e1 >>=
>       unify p "expression" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             m boolType
>     (cx',ty) <- tcExpr m tcEnv p e2
>     cx'' <-
>       tcExpr m tcEnv p e3 >>=
>       unify p "expression" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e3) m ty
>     return (cx ++ cx' ++ cx'',ty)
> tcExpr m tcEnv p (Case e as) =
>   do
>     (cx,tyLhs) <- tcExpr m tcEnv p e
>     tyRhs <- freshTypeVar
>     cxs <- mapM (tcAlt m tcEnv tyLhs tyRhs) as
>     return (cx ++ concat cxs,tyRhs)

> tcAlt :: ModuleIdent -> TCEnv -> Type -> Type -> Alt -> TcState Context
> tcAlt m tcEnv tyLhs tyRhs a@(Alt p t rhs) =
>   do
>     cx <-
>       tcConstrTerm m tcEnv noSigs p t >>=
>       unify p "case pattern" (doc $-$ text "Term:" <+> ppConstrTerm 0 t)
>             m tyLhs
>     cx' <- tcRhs m tcEnv rhs >>= unify p "case branch" doc m tyRhs
>     return (cx ++ cx')
>   where doc = ppAlt a

> tcQual :: ModuleIdent -> TCEnv -> Position -> Statement -> TcState Context
> tcQual m tcEnv p (StmtExpr e) =
>   tcExpr m tcEnv p e >>= unify p "guard" (ppExpr 0 e) m boolType
> tcQual m tcEnv p q@(StmtBind t e) =
>   do
>     (cx,ty) <- tcConstrTerm m tcEnv noSigs p t
>     cx' <-
>       tcExpr m tcEnv p e >>=
>       unify p "generator" (ppStmt q $-$ text "Term:" <+> ppExpr 0 e)
>             m (listType ty)
>     return (cx ++ cx')
> tcQual m tcEnv p (StmtDecl ds) = tcDecls m tcEnv ds

> tcStmt :: ModuleIdent -> TCEnv -> Position -> Statement -> TcState Context
> tcStmt m tcEnv p (StmtExpr e) =
>   do
>     alpha <- freshTypeVar
>     tcExpr m tcEnv p e >>= unify p "statement" (ppExpr 0 e) m (ioType alpha)
> tcStmt m tcEnv p st@(StmtBind t e) =
>   do
>     (cx,ty) <- tcConstrTerm m tcEnv noSigs p t
>     cx' <-
>       tcExpr m tcEnv p e >>=
>       unify p "statement" (ppStmt st $-$ text "Term:" <+> ppExpr 0 e)
>             m (ioType ty)
>     return (cx ++ cx')
> tcStmt m tcEnv p (StmtDecl ds) = tcDecls m tcEnv ds

\end{verbatim}
The function \texttt{tcArrow} checks that its argument can be used as
an arrow type $\alpha\rightarrow\beta$ and returns the pair
$(\alpha,\beta)$. Similarly, the function \texttt{tcBinary} checks
that its argument can be used as an arrow type
$\alpha\rightarrow\beta\rightarrow\gamma$ and returns the triple
$(\alpha,\beta,\gamma)$.
\begin{verbatim}

> tcArrow :: Position -> String -> Doc -> ModuleIdent -> (Context,Type)
>         -> TcState (Context,Type,Type)
> tcArrow p what doc m (cx,ty) =
>   do
>     theta <- liftSt fetchSt
>     unaryArrow (subst theta ty)
>   where unaryArrow (TypeArrow ty1 ty2) = return (cx,ty1,ty2)
>         unaryArrow (TypeVariable tv) =
>           do
>             alpha <- freshTypeVar
>             beta <- freshTypeVar
>             liftSt (updateSt_ (bindVar tv (TypeArrow alpha beta)))
>             return (cx,alpha,beta)
>         unaryArrow ty = errorAt p (nonFunctionType what doc m ty)

> tcBinary :: Position -> String -> Doc -> ModuleIdent -> (Context,Type)
>          -> TcState (Context,Type,Type,Type)
> tcBinary p what doc m ty = tcArrow p what doc m ty >>= uncurry3 binaryArrow
>   where binaryArrow cx ty1 (TypeArrow ty2 ty3) = return (cx,ty1,ty2,ty3)
>         binaryArrow cx ty1 (TypeVariable tv) =
>           do
>             beta <- freshTypeVar
>             gamma <- freshTypeVar
>             liftSt (updateSt_ (bindVar tv (TypeArrow beta gamma)))
>             return (cx,ty1,beta,gamma)
>         binaryArrow _ ty1 ty2 =
>           errorAt p (nonBinaryOp what doc m (TypeArrow ty1 ty2))

\end{verbatim}
\paragraph{Unification}
The unification uses Robinson's algorithm (cf., e.g., Chap.~9
of~\cite{PeytonJones87:Book}).
\begin{verbatim}

> unify :: Position -> String -> Doc -> ModuleIdent -> Type -> (Context,Type)
>       -> TcState Context
> unify p what doc m ty1 (cx,ty2) =
>   do
>     theta <- liftSt fetchSt
>     let ty1' = subst theta ty1
>     let ty2' = subst theta ty2
>     either (errorAt p . typeMismatch what doc m ty1' ty2')
>            (liftSt . updateSt_ . compose)
>            (unifyTypes m ty1' ty2')
>     reduceContext p what doc m cx

> unifyTypes :: ModuleIdent -> Type -> Type -> Either Doc TypeSubst
> unifyTypes _ (TypeVariable tv1) (TypeVariable tv2)
>   | tv1 == tv2 = Right idSubst
>   | otherwise = Right (bindSubst tv1 (TypeVariable tv2) idSubst)
> unifyTypes m (TypeVariable tv) ty
>   | tv `elem` typeVars ty = Left (recursiveType m tv ty)
>   | otherwise = Right (bindSubst tv ty idSubst)
> unifyTypes m ty (TypeVariable tv)
>   | tv `elem` typeVars ty = Left (recursiveType m tv ty)
>   | otherwise = Right (bindSubst tv ty idSubst)
> unifyTypes _ (TypeGuard tv1) (TypeGuard tv2)
>   | tv1 == tv2 = Right idSubst
>   | otherwise = Right (bindSubst tv1 (TypeGuard tv2) idSubst)
> unifyTypes m (TypeGuard tv) ty =
>   foldr (choose . unifyTypes m ty)
>         (Left (incompatibleTypes m ty (head guardTypes)))
>         guardTypes
>   where choose (Left _) theta' = theta'
>         choose (Right theta) _ = Right (bindSubst tv ty theta)
> unifyTypes m ty (TypeGuard tv) =
>   foldr (choose . unifyTypes m ty)
>         (Left (incompatibleTypes m ty (head guardTypes)))
>         guardTypes
>   where choose (Left _) theta' = theta'
>         choose (Right theta) _ = Right (bindSubst tv ty theta)
> unifyTypes m (TypeConstructor tc1 tys1) (TypeConstructor tc2 tys2)
>   | tc1 == tc2 = unifyTypeLists m tys1 tys2
> unifyTypes m (TypeArrow ty11 ty12) (TypeArrow ty21 ty22) =
>   unifyTypeLists m [ty11,ty12] [ty21,ty22]
> unifyTypes _ (TypeSkolem k1) (TypeSkolem k2)
>   | k1 == k2 = Right idSubst
> unifyTypes m ty1 ty2 = Left (incompatibleTypes m ty1 ty2)

> unifyTypeLists :: ModuleIdent -> [Type] -> [Type] -> Either Doc TypeSubst
> unifyTypeLists _ [] _ = Right idSubst
> unifyTypeLists _ _ [] = Right idSubst
> unifyTypeLists m (ty1:tys1) (ty2:tys2) =
>   either Left (unifyTypesTheta m ty1 ty2) (unifyTypeLists m tys1 tys2)
>   where unifyTypesTheta m ty1 ty2 theta =
>           either Left (Right . flip compose theta)
>                  (unifyTypes m (subst theta ty1) (subst theta ty2))

\end{verbatim}
After performing a unification, the resulting substitution is applied
to the current context and the resulting context is subject to a
context reduction. This context reduction retains all predicates whose
types are simple variables and for all other types checks whether an
instance exists. A minor complication arises due to guard types, which
are used to delay the type selection for guard expressions. Since the
set of admissible types of a guard type may be restricted by the
current context after the context reduction, this may cause a further
extension of the current substitution.

\ToDo{Replace guard types by overloading with type classes.}
\begin{verbatim}

> reduceContext :: Position -> String -> Doc -> ModuleIdent
>               -> Context -> TcState Context
> reduceContext p what doc m cx =
>   do
>     iEnv <- liftSt (liftSt envRt)
>     theta <- liftSt fetchSt
>     let cx' = nub (map (subst theta) cx)
>         (cx1,cx2) = partition (\(TypePred _ ty) -> isTypeVar ty) cx'
>     mapM_ (checkTypePred p what doc m iEnv) cx2
>     return cx1
>   where isTypeVar (TypeConstructor _ _) = False
>         isTypeVar (TypeVariable _) = True
>         isTypeVar (TypeGuard _) = False
>         isTypeVar (TypeArrow _ _) = False
>         isTypeVar (TypeSkolem _) = False

> checkTypePred :: Position -> String -> Doc -> ModuleIdent -> InstEnv
>               -> TypePred -> TcState ()
> checkTypePred p what doc m iEnv (TypePred cls ty) =
>   case ty of
>     TypeGuard tv ->
>       case filter hasInstance guardTypes of
>         [] -> errorAt p (noInstance what doc m cls ty)
>         [ty'] -> liftSt (updateSt_ (bindSubst tv ty'))
>         _ -> return ()
>     _ -> unless (hasInstance ty) (errorAt p (noInstance what doc m cls ty))
>   where hasInstance (TypeConstructor tc _) = CT cls tc `elemSet` iEnv
>         hasInstance (TypeVariable _) = True
>         hasInstance (TypeGuard _) = any hasInstance guardTypes
>         hasInstance (TypeArrow _ _) = CT cls qArrowId `elemSet` iEnv
>         hasInstance (TypeSkolem _) = False

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

> checkSkolems :: Position -> ModuleIdent -> Doc -> Set Int -> Type
>              -> TcState ()
> checkSkolems p m what fs ty =
>   do
>     ty' <- liftM (flip subst ty) (liftSt fetchSt)
>     unless (all (`elemSet` fs) (typeSkolems ty'))
>            (errorAt p (skolemEscapingScope m what ty'))

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

> freshGuard :: TcState Type
> freshGuard = freshVar TypeGuard

> freshSkolem :: TcState Type
> freshSkolem = fresh TypeSkolem

> inst :: TypeScheme -> TcState (Context,Type)
> inst (ForAll n (QualType cx ty)) =
>   do
>     tys <- replicateM n freshTypeVar
>     return (map (expandAliasType tys) cx,expandAliasType tys ty)

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
latter is given by \texttt{gen}'s first argument. Note that
\texttt{gen} carefully cleans up the context so that only universally
quantified type variables are constrained.
\begin{verbatim}

> gen :: Set Int -> Context -> Type -> TypeScheme
> gen fvs cx ty = ForAll (length tvs) (subst tvs' (QualType cx' ty))
>   where tvs = [tv | tv <- nub (typeVars ty), tv `notElemSet` fvs]
>         tvs' = foldr2 bindSubst idSubst tvs (map TypeVariable [0..])
>         cx' = fst (splitContext (fromListSet tvs) cx)

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
Error functions.
\begin{verbatim}

> polymorphicVar :: Ident -> String
> polymorphicVar v = "Variable " ++ name v ++ " cannot have polymorphic type"

> typeSigTooGeneral :: ModuleIdent -> Doc -> QualTypeExpr
>                   -> TypeScheme -> String
> typeSigTooGeneral m what ty sigma = show $
>   vcat [text "Type signature too general", what,
>         text "Inferred type:" <+> ppTypeScheme m sigma,
>         text "Type signature:" <+> ppQualTypeExpr ty]

> wrongArity :: QualIdent -> Int -> Int -> String
> wrongArity c arity argc = show $
>   hsep [text "Constructor", ppQIdent c, text "requires",
>         int arity, text (plural arity "argument"),
>         text "in patterns, but is applied to", int argc]
>   where plural n x = if n == 1 then x else x ++ "s"

> nonFunctionType :: String -> Doc -> ModuleIdent -> Type -> String
> nonFunctionType what doc m ty = show $
>   vcat [text "Type error in" <+> text what, doc,
>         text "Type:" <+> ppType m ty,
>         text "Cannot be applied"]

> nonBinaryOp :: String -> Doc -> ModuleIdent -> Type -> String
> nonBinaryOp what doc m ty = show $
>   vcat [text "Type error in" <+> text what, doc,
>         text "Type:" <+> ppType m ty,
>         text "Cannot be used as binary operator"]

> typeMismatch :: String -> Doc -> ModuleIdent -> Type -> Type -> Doc -> String
> typeMismatch what doc m ty1 ty2 reason = show $
>   vcat [text "Type error in" <+> text what, doc,
>         text "Inferred type:" <+> ppType m ty2,
>         text "Expected type:" <+> ppType m ty1,
>         reason]

> skolemEscapingScope :: ModuleIdent -> Doc -> Type -> String
> skolemEscapingScope m what ty = show $
>   vcat [text "Existential type escapes out of its scope", what,
>         text "Type:" <+> ppType m ty]

> invalidCType :: String -> ModuleIdent -> Type -> String
> invalidCType what m ty = show $
>   vcat [text ("Invalid " ++ what ++ " type in foreign declaration:"),
>         ppType m ty]

> recursiveType :: ModuleIdent -> Int -> Type -> Doc
> recursiveType m tv ty = incompatibleTypes m (TypeVariable tv) ty

> incompatibleTypes :: ModuleIdent -> Type -> Type -> Doc
> incompatibleTypes m ty1 ty2 =
>   sep [text "Types" <+> ppType m ty1,
>        nest 2 (text "and" <+> ppType m ty2),
>        text "are incompatible"]

> ambiguousType :: String -> Doc -> ModuleIdent -> [Type] -> Context -> Type
>               -> String
> ambiguousType what doc m tvs cx ty = show $
>   vcat [text "Ambiguous type variable" <> plural tvs <+>
>           list (map (ppType m) tvs) <+> text "in type",
>         ppQualType m (canonType (QualType cx ty)),
>         text "inferred for" <+> text what, doc]
>   where plural (_:xs) = if null xs then empty else char 's'
>         list [x] = x
>         list [x1,x2] = x1 <+> text "and" <+> x2
>         list xs = hsep (map (<> comma) (init xs)) <+> text "and" <+> last xs

> noInstance :: String -> Doc -> ModuleIdent -> QualIdent -> Type -> String
> noInstance what doc m cls ty = show $
>   vcat [sep [text "Missing instance for",
>              ppQIdent (qualUnqualify m cls) <+> ppTypeExpr 2 (fromType m ty),
>              text "in" <+> text what],
>         doc]

\end{verbatim}
