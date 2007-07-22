% -*- LaTeX -*-
% $Id: TypeCheck.lhs 2405 2007-07-22 17:43:40Z wlux $
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
current module to the type environment.
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

> typeCheckGoal :: Bool -> ModuleIdent -> TCEnv -> InstEnv -> ValueEnv -> Goal a
>               -> Error (ValueEnv,Context,Goal Type)
> typeCheckGoal forEval m tcEnv iEnv tyEnv g =
>   run (do
>          (cx,g') <- tcGoal forEval m tcEnv g
>          tyEnv' <- fetchSt
>          theta <- liftSt fetchSt
>          return (subst theta tyEnv',cx,fmap (subst theta) g'))
>       iEnv
>       tyEnv

\end{verbatim}
The type checker makes use of nested state monads in order to maintain
the type environment, the current substitution, and a counter, which
is used for generating fresh type variables. In addition, the instance
environment is passed around using a reader monad.
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
>           bindConstr (const . NewtypeConstructor) m tcEnv cx tc tvs c [ty]
> bindTypeValues _ _ (TypeDecl _ _ _ _) tyEnv = tyEnv
> bindTypeValues m tcEnv (ClassDecl _ _ cls tv ds) tyEnv = foldr bind tyEnv ds
>   where cls' = qualifyWith m cls
>         bind (MethodFixity _ _ _ _) = id
>         bind (MethodSig _ fs ty) = bindMethods m tcEnv cls' tv fs ty
>         bind (MethodDecl _ _ _) = id
>         bind (TrustMethod _ _ _) = id
> bindTypeValues _ _ (InstanceDecl _ _ _ _ _) tyEnv = tyEnv
> bindTypeValues _ _ (BlockDecl _) tyEnv = tyEnv

> bindConstr :: (QualIdent -> Int -> TypeScheme -> ValueInfo) -> ModuleIdent
>            -> TCEnv -> [ClassAssert] -> Ident -> [Ident] -> Ident
>            -> [TypeExpr] -> ValueEnv -> ValueEnv
> bindConstr f m tcEnv cx tc tvs c tys =
>   globalBindTopEnv m c (f (qualifyWith m c) (length tys) (typeScheme ty))
>   where ty = expandConstrType tcEnv cx (qualifyWith m tc) tvs tys

> bindMethods :: ModuleIdent -> TCEnv -> QualIdent -> Ident -> [Ident]
>             -> QualTypeExpr -> ValueEnv -> ValueEnv
> bindMethods m tcEnv cls tv fs ty tyEnv =
>   foldr (bindMethod m (typeScheme ty')) tyEnv fs
>   where ty' = expandMethodType tcEnv cls tv ty

> bindMethod :: ModuleIdent -> TypeScheme -> Ident -> ValueEnv -> ValueEnv
> bindMethod m ty f = globalBindTopEnv m f (Value (qualifyWith m f) 0 ty)

\end{verbatim}
\paragraph{Type Signatures}
The type checker collects type signatures in a flat environment. The
types are not expanded so that the signatures can be used in the error
messages which are printed when an inferred type is less general than
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
group, first the type environment is extended with new bindings for
all variables and functions defined in the group. Next, each
declaration is checked in the extended type environment. Finally, the
types of all defined functions are generalized. The generalization
step will also check that the type signatures given by the user match
the inferred types.

The presence of unbound logical variables necessitates a monomorphism
restriction that prohibits unsound functions like
\begin{verbatim}
  bug = x =:= 1 & x =:= 'a' where x free
\end{verbatim}
This declaration would be accepted by the type checker if \verb|x|'s
type were generalized to $\forall\alpha.\alpha$. Curry's type system
(cf.\ Sect.~4.2 of~\cite{Hanus:Report}) is presently defined for
programs that have been transformed into a set of global, possibly
mutually recursive function declarations, where local declarations are
used only to introduce logical variables. Under this transformation,
the types of all local variables are monomorphic because the
Hindley-Milner type system does not generalize the types of
lambda-bound variables and logical variables are required to be
monomorphic by the existential rule of Curry's type system.

While sound, Curry's present type system is overly restrictive. Some
perfectly valid declarations like
\begin{verbatim}
  ok = (1:nil, 'a':nil) where nil = []
\end{verbatim}
are rejected by the compiler. A safe extension of Curry's type system
would allow polymorphic generalization for variables that are bound to
expressions containing no free variables. Yet, identifying ground
terms in general requires a complex semantic analysis and therefore
should not be a prerequisite for type checking. A good compromise is
to allow polymorphic generalization for variables that are bound to
expressions for which the compiler can easily prove that they do not
contain free variables. The distinction between expansive and
non-expansive expressions comes to help here, which is used by ML-like
languages in order to ensure type soundness in the presence of
imperative effects~\cite{WrightFelleisen94:TypeSoundness}. In Curry, a
non-expansive expression is either
\begin{itemize}\label{non-expansive}
\item a literal,
\item a variable,
\item an application of a constructor with arity $n$ to at most $n$
  non-expansive expressions,
\item an application of a function with arity $n$ to at most $n-1$
  non-expansive expressions, or
\item a let expression whose body is a non-expansive expression and
  whose local declarations are either function declarations or
  variable declarations of the form \texttt{$x$=$e$} where $e$ is a
  non-expansive expression, or
\item an expression whose desugared form is one of the above.
\end{itemize}
At first it may seem strange that variables are included in the list
above because a variable may be bound to a logical variable. However,
this is no problem because type variables that are present among the
typing assumptions of the environment enclosing a let expression
cannot be generalized.

Recently, Garrigue has shown that ML's value restriction can be lifted
a bit and that generalizing type variables that appear only in
covariant positions is sound~\cite{Garrigue04:ValueRestriction}.
Obviously, this generalization does not hold for Curry with
\texttt{let x = unknown in x} being the canonical counter-example.

While generalizing the types of variables bound to a non-expansive
expression, we must be careful not to quantify any type variables
with type class constraints. The technical reason for this
restriction, which is just Haskell's monomorphism restriction
(cf.\ Sect.~4.5.5 of~\cite{PeytonJones03:Haskell}), is that only a
single dictionary can be used for each overloaded type variable on the
right hand side of a pattern declaration. As in Haskell, this
restriction can be overridden with an explicit type signature.

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
> tcDeclGroup m tcEnv _ cx [ForeignDecl p cc s ie f ty] =
>   do
>     tcForeignFunct m tcEnv p cc ie f ty
>     return (cx,[ForeignDecl p cc s ie f ty])
> tcDeclGroup m tcEnv sigs cx [FreeDecl p vs] =
>   do
>     bindDeclVars m tcEnv sigs p vs
>     return (cx,[FreeDecl p vs])
> tcDeclGroup m tcEnv sigs cx ds =
>   do
>     tyEnv0 <- fetchSt
>     mapM_ (bindDecl m tcEnv sigs) ds
>     (cx',ds') <- mapAccumM (tcDecl m tcEnv) cx ds
>     tyEnv <- fetchSt
>     theta <- liftSt fetchSt
>     let vs = [v | PatternDecl _ t rhs <- ds,
>                   not (isVariablePattern t && isNonExpansive tcEnv tyEnv rhs),
>                   v <- bv t]
>         vs' = [v | PatternDecl _ (VariablePattern _ v) rhs <- ds,
>                    isNonExpansive tcEnv tyEnv rhs]
>         tvs = concatMap (typeVars . subst theta . flip varType tyEnv) vs
>         tvs' = concatMap (typeVars . subst theta . flip varType tyEnv) vs'
>         fvs = foldr addToSet (fvEnv (subst theta tyEnv0))
>                     (tvs ++ filter (`elem` concatMap typeVars cx') tvs')
>         (gcx,lcx) = splitContext fvs cx'
>     ds'' <- mapM (uncurry3 (dfltDecl tcEnv) . mergeContext lcx theta) ds'
>     ds''' <- mapM (uncurry3 (genDecl m tcEnv tyEnv sigs fvs)) ds''
>     return (gcx,ds''')
>   where mergeContext cx1 theta (cx2,ty,d) = (cx1 ++ cx2,subst theta ty,d)

> bindDecl :: ModuleIdent -> TCEnv -> SigEnv -> Decl a -> TcState ()
> bindDecl m tcEnv sigs (FunctionDecl p f eqs) =
>   case lookupEnv f sigs of
>     Just ty ->
>       updateSt_ (bindFun m f n (typeScheme (expandPolyType tcEnv ty)))
>     Nothing ->
>       replicateM (n + 1) freshTypeVar >>=
>       updateSt_ . bindFun m f n . monoType . foldr1 TypeArrow
>   where n = eqnArity (head eqs)
> bindDecl m tcEnv sigs (PatternDecl p t _) =
>   case t of
>     VariablePattern _ v -> bindDeclVar True m tcEnv sigs p v
>     _ -> bindDeclVars m tcEnv sigs p (bv t)

> bindDeclVars :: ModuleIdent -> TCEnv -> SigEnv -> Position -> [Ident]
>              -> TcState ()
> bindDeclVars m tcEnv sigs p = mapM_ (bindDeclVar False m tcEnv sigs p)

> bindDeclVar :: Bool -> ModuleIdent -> TCEnv -> SigEnv -> Position -> Ident
>             -> TcState ()
> bindDeclVar poly m tcEnv sigs p v =
>   case lookupEnv v sigs of
>     Just ty
>       | poly || null (fv ty) ->
>           updateSt_ (bindFun m v 0 (typeScheme (expandPolyType tcEnv ty)))
>       | otherwise -> errorAt p (polymorphicVar v)
>     Nothing -> bindLambdaVar m v

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
>     (cx',ty',t') <- tcConstrTerm tcEnv p t
>     (cx'',rhs') <-
>       tcRhs m tcEnv rhs >>=
>       unifyDecl p "pattern declaration" (ppDecl d) tcEnv tyEnv0 (cx++cx') ty'
>     return (cx'',([],ty',PatternDecl p t' rhs'))

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
>     (cx,eq') <-
>       tcEqn m tcEnv p lhs rhs >>=
>       unifyDecl p "function declaration" (ppEquation eq) tcEnv tyEnv0 [] ty
>     checkSkolems p tcEnv (text "Function:" <+> ppIdent f) fs cx ty
>     return (cx,eq')

> tcEqn :: ModuleIdent -> TCEnv -> Position -> Lhs a -> Rhs a
>       -> TcState (Context,Type,Equation Type)
> tcEqn m tcEnv p lhs rhs =
>   do
>     bindLambdaVars m lhs
>     (cx,tys,lhs') <- tcLhs tcEnv p lhs
>     (cx',ty,rhs') <- tcRhs m tcEnv rhs
>     return (cx ++ cx',foldr TypeArrow ty tys,Equation p lhs' rhs')

> bindLambdaVars :: QuantExpr t => ModuleIdent -> t -> TcState ()
> bindLambdaVars m t = mapM_ (bindLambdaVar m) (bv t)

> bindLambdaVar :: ModuleIdent -> Ident -> TcState ()
> bindLambdaVar m v = freshTypeVar >>= updateSt_ . bindFun m v 0 . monoType

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
>     checkSkolems p tcEnv (text "Goal:" <+> ppExpr 0 e) tvs cx ty
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
type signature, the declared type must be too general. Note that it is
possible that the inferred context is only a subset of the declared
context because the context of a function's type signature is
(deliberately) ignored in \texttt{tcFunctionDecl} above.

As in Haskell, the restriction that the of constrained type variables
in the type of a variable declaration \texttt{$x$=$e$} cannot be
generalized, can be overridden with an explicit type signature.
However, this also means that the result of expression $e$ can no
longer be shared among the different occurrences of variable $x$,
i.e., the declaration \texttt{$x$=$e$} must be interpreted as a
(nullary) function definition. The variable declaration case of
\texttt{genDecl} takes care of this.

Note that the transformation of a variable declaration into a nullary
function declaration breaks the invariant that nullary functions can
be defined only at the top-level. However, keep in mind that this can
happen only if the variable declaration's right hand side is
non-expansive and that for a non-expansive expression is does not
matter whether it its evaluation is shared or not.

\ToDo{Strictly speaking this is not true for numeric literals, which
  are just abbreviations for \texttt{Prelude.fromInt}~$i$ and
  \texttt{Prelude.fromFloat}~$f$, respectively. Therefore, the
  compiler should either consider numeric literals expansive or ensure
  that the \texttt{fromInt} and \texttt{fromFloat} instance method
  definitions are deterministic.}
\begin{verbatim}

> genDecl :: ModuleIdent -> TCEnv -> ValueEnv -> SigEnv -> Set Int -> Context
>         -> Type -> Decl a -> TcState (Decl a)
> genDecl m tcEnv _ sigs fvs cx ty d@(FunctionDecl p f eqs) =
>   case lookupEnv f sigs of
>     Just sigTy
>       | checkTypeSig tcEnv (expandPolyType tcEnv sigTy) sigma -> return d
>       | otherwise -> errorAt p (typeSigTooGeneral tcEnv what sigTy sigma)
>     Nothing ->
>       updateSt_ (rebindFun m f (eqnArity (head eqs)) sigma) >> return d
>   where what = text "Function:" <+> ppIdent f
>         sigma = gen fvs cx ty
> genDecl m tcEnv tyEnv sigs fvs cx ty d@(PatternDecl p t rhs) =
>   case t of
>     VariablePattern _ v ->
>       case lookupEnv v sigs of
>         Just sigTy
>           | sigma == typeScheme (expandPolyType tcEnv sigTy) ->
>               return (if null cx then d else funDecl p v rhs)
>           | otherwise -> errorAt p (typeSigTooGeneral tcEnv what sigTy sigma)
>           where funDecl p f rhs =
>                   FunctionDecl p f [Equation p (FunLhs f []) rhs]
>         Nothing
>           | poly -> updateSt_ (rebindFun m v 0 sigma) >> return d
>           | otherwise -> return d
>       where what = text "Variable: " <+> ppIdent v
>             poly = isNonExpansive tcEnv tyEnv rhs
>             sigma = if poly then gen fvs cx ty else monoType ty
>     _ -> return d

> checkTypeSig :: TCEnv -> QualType -> TypeScheme -> Bool
> checkTypeSig tcEnv (QualType sigCx sigTy) (ForAll _ (QualType cx ty)) =
>   ty == sigTy && all (`elem` maxContext tcEnv sigCx) cx

> class Binding a where
>   isNonExpansive :: TCEnv -> ValueEnv -> a -> Bool

> instance Binding a => Binding [a] where
>   isNonExpansive tcEnv tyEnv = all (isNonExpansive tcEnv tyEnv)

> instance Binding (Decl a) where
>   isNonExpansive _ _ (InfixDecl _ _ _ _) = True
>   isNonExpansive _ _ (TypeSig _ _ _) = True
>   isNonExpansive _ _ (FunctionDecl _ _ _) = True
>   isNonExpansive _ _ (ForeignDecl _ _ _ _ _ _) = True
>   isNonExpansive tcEnv tyEnv (PatternDecl _ t rhs) =
>     isVariablePattern t && isNonExpansive tcEnv tyEnv rhs
>   isNonExpansive _ _ (FreeDecl _ _) = False
>   isNonExpansive _ _ (TrustAnnot _ _ _) = True

> instance Binding (Rhs a) where
>   isNonExpansive tcEnv tyEnv (SimpleRhs _ e ds) =
>     isNonExpansive tcEnv tyEnv ds && isNonExpansive tcEnv tyEnv e
>   isNonExpansive _ _ (GuardedRhs _ _) = False

> instance Binding (Expression a) where
>   isNonExpansive tcEnv tyEnv = isNonExpansiveApp tcEnv tyEnv 0

> isNonExpansiveApp :: TCEnv -> ValueEnv -> Int -> Expression a -> Bool
> isNonExpansiveApp _ _ _ (Literal _ _) = True
> isNonExpansiveApp _ tyEnv n (Variable _ v)
>   | isRenamed (unqualify v) = n == 0 || n < arity v tyEnv
>   | otherwise = n < arity v tyEnv
> isNonExpansiveApp _ _ _ (Constructor _ _) = True
> isNonExpansiveApp tcEnv tyEnv n (Paren e) =
>   isNonExpansiveApp tcEnv tyEnv n e
> isNonExpansiveApp tcEnv tyEnv n (Typed e _) =
>   isNonExpansiveApp tcEnv tyEnv n e
> isNonExpansiveApp tcEnv tyEnv _ (Tuple es) =
>   isNonExpansive tcEnv tyEnv es
> isNonExpansiveApp tcEnv tyEnv _ (List _ es) =
>   isNonExpansive tcEnv tyEnv es
> isNonExpansiveApp tcEnv tyEnv n (Apply f e) =
>   isNonExpansive tcEnv tyEnv e && isNonExpansiveApp tcEnv tyEnv (n + 1) f
> isNonExpansiveApp tcEnv tyEnv n (InfixApply e1 op e2) =
>   isNonExpansiveApp tcEnv tyEnv (n + 2) (infixOp op) &&
>   isNonExpansive tcEnv tyEnv e1 && isNonExpansive tcEnv tyEnv e2
> isNonExpansiveApp tcEnv tyEnv n (LeftSection e op) =
>   isNonExpansiveApp tcEnv tyEnv (n + 1) (infixOp op) &&
>   isNonExpansive tcEnv tyEnv e
> isNonExpansiveApp _ _ n (Lambda _ ts _) = n < length ts
> isNonExpansiveApp tcEnv tyEnv n (Let ds e) =
>   isNonExpansive tcEnv tyEnv ds && isNonExpansiveApp tcEnv tyEnv n e
> isNonExpansiveApp _ _ _ _ = False

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

When checking inferred method types against their expected types, we
have to be careful because the class' type variable is always assigned
index 0 in the method types recorded in the type environment. However,
in the inferred type scheme returned from \texttt{tcMethodDecl}, type
variables are assigned indices in the order of their occurrence. In
order to avoid incorrectly reporting errors when the type class
variable is not the first variable that appears in a method's type,
\texttt{tcInstMethodDecl} normalizes the expected method type before
applying \texttt{checkInstMethodType} to it and
\texttt{checkClassMethodType} uses \texttt{expandPolyType} instead of
\texttt{expandMethodType} in order to convert the method's type
signature. Unfortunately, this also means that the compiler has to add
the class type constraint explicitly to the type signature, which is
done while collecting the type signatures in the \texttt{ClassDecl}
case of \texttt{tcTopDecl}.
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
>   where sigs = foldr (bindTypeSigs . typeSig (qualify cls) tv) noSigs ods
>         (vds,ods) = partition isMethodDecl ds
>         typeSig _ _ (MethodFixity p fix pr ops) = InfixDecl p fix pr ops
>         typeSig cls tv (MethodSig p fs (QualTypeExpr cx ty)) =
>           TypeSig p fs (QualTypeExpr (ClassAssert cls tv [] : cx) ty)
>         typeSig _ _ (TrustMethod p tr fs) = TrustAnnot p tr fs
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
>     methTy <- liftM (classMethodType (qualifyWith m) d) fetchSt
>     (ty',d') <- tcMethodDecl m tcEnv methTy d
>     checkClassMethodType tcEnv (classMethodSig sigs d) ty' d'

> checkClassMethodType :: TCEnv -> QualTypeExpr -> TypeScheme -> Decl Type
>                      -> TcState (MethodDecl Type)
> checkClassMethodType tcEnv sigTy sigma (FunctionDecl p f eqs)
>   | checkTypeSig tcEnv (expandPolyType tcEnv sigTy) sigma =
>       return (MethodDecl p f eqs)
>   | otherwise = errorAt p (typeSigTooGeneral tcEnv what sigTy sigma)
>   where what = text "Method:" <+> ppIdent f

> tcInstMethodDecl :: ModuleIdent -> TCEnv -> QualIdent -> QualType
>                  -> MethodDecl a -> TcState (MethodDecl Type)
> tcInstMethodDecl m tcEnv cls instTy d =
>   do
>     methTy <- liftM (instMethodType (qualifyLike cls) instTy d) fetchSt
>     (ty',d') <- tcMethodDecl m tcEnv (typeScheme methTy) d
>     checkInstMethodType tcEnv (normalize 0 methTy) ty' d'

> checkInstMethodType :: TCEnv -> QualType -> TypeScheme -> Decl Type
>                     -> TcState (MethodDecl Type)
> checkInstMethodType tcEnv methTy sigma (FunctionDecl p f eqs)
>   | checkTypeSig tcEnv methTy sigma = return (MethodDecl p f eqs)
>   | otherwise = errorAt p (methodSigTooGeneral tcEnv what methTy sigma)
>   where what = text "Method:" <+> ppIdent f

> tcMethodDecl :: ModuleIdent -> TCEnv -> TypeScheme -> MethodDecl a
>              -> TcState (TypeScheme,Decl Type)
> tcMethodDecl m tcEnv methTy (MethodDecl p f eqs) =
>   do
>     updateSt_ (bindFun m f (eqnArity (head eqs)) methTy)
>     (cx,(ty,d')) <- tcFunctionDecl "method" m tcEnv [] methTy p f eqs
>     theta <- liftSt fetchSt
>     return (gen zeroSet cx (subst theta ty),d')

> classMethodSig :: SigEnv -> MethodDecl a -> QualTypeExpr
> classMethodSig sigs (MethodDecl _ f _) =
>   fromJust (lookupEnv (unRenameIdent f) sigs)

> classMethodType :: (Ident -> QualIdent) -> MethodDecl a -> ValueEnv
>                 -> TypeScheme
> classMethodType qualify (MethodDecl _ f _) tyEnv =
>   funType (qualify (unRenameIdent f)) tyEnv

> instMethodType :: (Ident -> QualIdent) -> QualType -> MethodDecl a -> ValueEnv
>                -> QualType
> instMethodType qualify (QualType cx ty) d tyEnv =
>   contextMap (cx ++) (instanceType ty (contextMap tail ty'))
>   where ForAll _ ty' = classMethodType qualify d tyEnv

\end{verbatim}
\paragraph{Foreign Functions}
Argument and result types of foreign functions using the
\texttt{ccall} calling convention are restricted to the basic types
\texttt{Bool}, \texttt{Char}, \texttt{Int}, \texttt{Float},
\texttt{Ptr}, \texttt{FunPtr}, and \texttt{StablePtr}. In addition,
$\texttt{IO}\;t$ is a legitimate result type when $t$ is either one of
the basic types or \texttt{()}. As an extension to the Haskell foreign
function interface specification~\cite{Chakravarty03:FFI}, the compiler
supports the non-standard \texttt{rawcall} calling convention, which
allows arbitrary argument and result types. However, in contrast
to the \texttt{ccall} calling convention, no marshaling takes place at
all even for the basic types (cf.\ Sect.~\ref{sec:il-compile} with
regard to marshalling). The type of a dynamic function wrapper is
restricted further to be of the form $\texttt{FunPtr}\;t \rightarrow
t$, where $t$ is a valid foreign function type, and the type of a
foreign address must be either $\texttt{Ptr}\;a$ or
$\texttt{FunPtr}\;a$, where $a$ is an arbitrary type.

Note that a foreign function with type $t_1 \rightarrow \dots
\rightarrow t_n \rightarrow t$ has arity $n$ unless the result type
$t$ is $\texttt{IO}\;t'$, in which case its arity will be $n+1$. This
special case reflects the fact that the type $\texttt{IO}\;t$ is
equivalent to $\emph{World}\rightarrow(t,\emph{World})$.
\begin{verbatim}

> tcForeignFunct :: ModuleIdent -> TCEnv -> Position -> CallConv
>                -> Maybe String -> Ident -> TypeExpr -> TcState ()
> tcForeignFunct m tcEnv p cc ie f ty =
>   do
>     checkForeignType cc (rawType ty')
>     updateSt_ (bindFun m f (foreignArity (rawType ty')) ty')
>   where ty' = typeScheme (expandPolyType tcEnv (QualTypeExpr [] ty))
>         checkForeignType cc ty
>           | cc == CallConvPrimitive = return ()
>           | ie == Just "dynamic" = checkCDynCallType tcEnv p cc ty
>           | maybe False ('&' `elem`) ie = checkCAddrType tcEnv p ty
>           | otherwise = checkCCallType tcEnv p cc ty
>         foreignArity ty
>           | isIO ty' = length tys + 1
>           | otherwise = length tys
>           where (tys,ty') = arrowUnapply ty
>         isIO (TypeApply (TypeConstructor tc) _) = tc == qIOId
>         isIO _ = False

> checkCCallType :: TCEnv -> Position -> CallConv -> Type -> TcState ()
> checkCCallType tcEnv p CallConvCCall (TypeArrow ty1 ty2)
>   | isCArgType ty1 = checkCCallType tcEnv p CallConvCCall ty2
>   | otherwise = errorAt p (invalidCType "argument" tcEnv ty1)
> checkCCallType tcEnv p CallConvCCall ty
>   | isCRetType ty = return ()
>   | otherwise = errorAt p (invalidCType "result" tcEnv ty)
> checkCCallType _ _ CallConvRawCall _ = return ()

> checkCDynCallType :: TCEnv -> Position -> CallConv -> Type -> TcState ()
> checkCDynCallType tcEnv p cc
>                   (TypeArrow (TypeApply (TypeConstructor tc) ty1) ty2)
>   | tc == qFunPtrId && ty1 == ty2 = checkCCallType tcEnv p cc ty1
> checkCDynCallType tcEnv p _ ty =
>   errorAt p (invalidCType "dynamic function" tcEnv ty)

> checkCAddrType :: TCEnv -> Position -> Type -> TcState ()
> checkCAddrType tcEnv p ty
>   | isCPtrType ty = return ()
>   | otherwise = errorAt p (invalidCType "static address" tcEnv ty)

> isCArgType :: Type -> Bool
> isCArgType (TypeConstructor tc) = tc `elem` cBasicTypeId
> isCArgType (TypeApply (TypeConstructor tc) _) =
>   tc `elem` qStablePtrId:cPointerTypeId
> isCArgType _ = False

> isCRetType :: Type -> Bool
> isCRetType (TypeApply (TypeConstructor tc) ty)
>   | tc == qIOId = ty == unitType || isCArgType ty
> isCRetType ty = isCArgType ty

> isCPtrType :: Type -> Bool
> isCPtrType (TypeApply (TypeConstructor tc) _) = tc `elem` cPointerTypeId
> isCPtrType _ = False

> cBasicTypeId, cPointerTypeId :: [QualIdent]
> cBasicTypeId = [qBoolId,qCharId,qIntId,qFloatId]
> cPointerTypeId = [qPtrId,qFunPtrId]

\end{verbatim}
\paragraph{Patterns and Expressions}
Note that overloaded literals are not supported in patterns.
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

> tcLhs :: TCEnv -> Position -> Lhs a -> TcState (Context,[Type],Lhs Type)
> tcLhs tcEnv p (FunLhs f ts) =
>   do
>     (cxs,tys,ts') <- liftM unzip3 $ mapM (tcConstrTerm tcEnv p) ts
>     return (concat cxs,tys,FunLhs f ts')
> tcLhs tcEnv p (OpLhs t1 op t2) =
>   do
>     (cx1,ty1,t1') <- tcConstrTerm tcEnv p t1
>     (cx2,ty2,t2') <- tcConstrTerm tcEnv p t2
>     return (cx1 ++ cx2,[ty1,ty2],OpLhs t1' op t2')
> tcLhs tcEnv p (ApLhs lhs ts) =
>   do
>     (cx,tys,lhs') <- tcLhs tcEnv p lhs
>     (cxs,tys',ts') <- liftM unzip3 $ mapM (tcConstrTerm tcEnv p) ts
>     return (cx ++ concat cxs,tys ++ tys',ApLhs lhs' ts')

> tcConstrTerm :: TCEnv -> Position -> ConstrTerm a
>              -> TcState (Context,Type,ConstrTerm Type)
> tcConstrTerm _ _ (LiteralPattern _ l) =
>   do
>     (cx,ty) <- tcLiteral False l
>     return (cx,ty,LiteralPattern ty l)
> tcConstrTerm _ _ (NegativePattern _ l) =
>   do
>     (cx,ty) <- tcLiteral False l
>     return (cx,ty,NegativePattern ty l)
> tcConstrTerm _ _ (VariablePattern _ v) =
>   do
>     (cx,ty) <- fetchSt >>= inst . varType v
>     return (cx,ty,VariablePattern ty v)
> tcConstrTerm tcEnv p t@(ConstructorPattern _ c ts) =
>   do
>     (cx,ty,ts') <- tcConstrApp tcEnv p (ppConstrTerm 0 t) c ts
>     return (cx,ty,ConstructorPattern ty c ts')
> tcConstrTerm tcEnv p t@(InfixPattern _ t1 op t2) =
>   do
>     (cx,ty,[t1',t2']) <- tcConstrApp tcEnv p (ppConstrTerm 0 t) op [t1,t2]
>     return (cx,ty,InfixPattern ty t1' op t2')
> tcConstrTerm tcEnv p (ParenPattern t) =
>   do
>     (cx,ty,t') <- tcConstrTerm tcEnv p t
>     return (cx,ty,ParenPattern t')
> tcConstrTerm tcEnv p (TuplePattern ts) =
>   do
>     (cxs,tys,ts') <- liftM unzip3 $ mapM (tcConstrTerm tcEnv p) ts
>     return (concat cxs,tupleType tys,TuplePattern ts')
> tcConstrTerm tcEnv p t@(ListPattern _ ts) =
>   do
>     ty <- freshTypeVar
>     (cxs,ts') <- liftM unzip $ mapM (tcElem (ppConstrTerm 0 t) ty) ts
>     return (concat cxs,listType ty,ListPattern (listType ty) ts')
>   where tcElem doc ty t =
>           tcConstrTerm tcEnv p t >>=
>           unify p "pattern" (doc $-$ text "Term:" <+> ppConstrTerm 0 t)
>                 tcEnv ty
> tcConstrTerm tcEnv p t@(AsPattern v t') =
>   do
>     (cx,ty) <- fetchSt >>= inst . varType v
>     (cx',t'') <-
>       tcConstrTerm tcEnv p t' >>=
>       unify p "pattern" (ppConstrTerm 0 t) tcEnv ty
>     return (cx ++ cx',ty,AsPattern v t'')
> tcConstrTerm tcEnv p (LazyPattern t) =
>   do
>     (cx,ty,t') <- tcConstrTerm tcEnv p t
>     return (cx,ty,LazyPattern t')

> tcConstrApp :: TCEnv -> Position -> Doc -> QualIdent -> [ConstrTerm a]
>             -> TcState (Context,Type,[ConstrTerm Type])
> tcConstrApp tcEnv p doc c ts =
>   do
>     tyEnv <- fetchSt
>     (cx,(tys,ty)) <- liftM (apSnd arrowUnapply) (skol (conType c tyEnv))
>     unless (length tys == n) (errorAt p (wrongArity c (length tys) n))
>     (cxs,ts') <- liftM unzip $ zipWithM (tcConstrArg tcEnv p doc) ts tys
>     return (cx ++ concat cxs,ty,ts')
>   where n = length ts

> tcConstrArg :: TCEnv -> Position -> Doc -> ConstrTerm a -> Type
>             -> TcState (Context,ConstrTerm Type)
> tcConstrArg tcEnv p doc t ty =
>   tcConstrTerm tcEnv p t >>=
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
>     (cx,ty) <- inst (typeScheme sigTy)
>     (cx',e') <-
>       tcExpr m tcEnv p e >>=
>       unifyDecl p "explicitly typed expression" (ppExpr 0 e) tcEnv tyEnv0
>                 [] ty
>     theta <- liftSt fetchSt
>     let fvs = fvEnv (subst theta tyEnv0)
>         sigma = gen fvs (snd (splitContext fvs cx')) (subst theta ty)
>     unless (checkTypeSig tcEnv sigTy sigma)
>       (errorAt p (typeSigTooGeneral tcEnv (text "Expression:" <+> ppExpr 0 e)
>                                     sig sigma))
>     return (cx ++ cx',ty,Typed e' sig)
>   where sigTy = expandPolyType tcEnv sig
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
> tcExpr m tcEnv _ (Lambda p ts e) =
>   do
>     bindLambdaVars m ts
>     (cxs,tys,ts') <- liftM unzip3 $ mapM (tcConstrTerm tcEnv p) ts
>     (cx',ty,e') <- tcExpr m tcEnv p e
>     return (concat cxs ++ cx',foldr TypeArrow ty tys,Lambda p ts' e')
> tcExpr m tcEnv p (Let ds e) =
>   do
>     (cx,ds') <- tcDecls m tcEnv ds
>     (cx',ty,e') <- tcExpr m tcEnv p e
>     return (cx ++ cx',ty,Let ds' e')
> tcExpr m tcEnv p (Do sts e) =
>   do
>     (cx,mTy) <- freshMonadType
>     (cxs,sts') <- liftM unzip $ mapM (tcStmt m tcEnv p mTy) sts
>     ty <- liftM (TypeApply mTy) freshTypeVar
>     (cx',e') <-
>       tcExpr m tcEnv p e >>= unify p "statement" (ppExpr 0 e) tcEnv ty
>     return (cx ++ concat cxs ++ cx',ty,Do sts' e')
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
>     bindLambdaVars m t
>     (cx,t') <-
>       tcConstrTerm tcEnv p t >>=
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
> tcQual m tcEnv _ q@(StmtBind p t e) =
>   do
>     bindLambdaVars m t
>     (cx,ty,t') <- tcConstrTerm tcEnv p t
>     (cx',e') <-
>       tcExpr m tcEnv p e >>=
>       unify p "generator" (ppStmt q $-$ text "Term:" <+> ppExpr 0 e)
>             tcEnv (listType ty)
>     return (cx ++ cx',StmtBind p t' e')
> tcQual m tcEnv _ (StmtDecl ds) =
>   do
>     (cx,ds') <- tcDecls m tcEnv ds
>     return (cx,StmtDecl ds')

> tcStmt :: ModuleIdent -> TCEnv -> Position -> Type -> Statement a
>        -> TcState (Context,Statement Type)
> tcStmt m tcEnv p mTy (StmtExpr e) =
>   do
>     alpha <- freshTypeVar
>     (cx',e') <-
>       tcExpr m tcEnv p e >>=
>       unify p "statement" (ppExpr 0 e) tcEnv (TypeApply mTy alpha)
>     return (cx',StmtExpr e')
> tcStmt m tcEnv _ mTy st@(StmtBind p t e) =
>   do
>     bindLambdaVars m t
>     (cx,ty,t') <- tcConstrTerm tcEnv p t
>     (cx',e') <-
>       tcExpr m tcEnv p e >>=
>       unify p "statement" (ppStmt st $-$ text "Term:" <+> ppExpr 0 e)
>             tcEnv (TypeApply mTy ty)
>     return (cx ++ cx',StmtBind p t' e')
> tcStmt m tcEnv _ _ (StmtDecl ds) =
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
> unifyTypes _ (TypeConstructor tc1) (TypeConstructor tc2)
>   | tc1 == tc2 = Right idSubst
> unifyTypes _ (TypeSkolem k1) (TypeSkolem k2)
>   | k1 == k2 = Right idSubst
> unifyTypes tcEnv (TypeApply ty11 ty12) (TypeApply ty21 ty22) =
>   case unifyTypes tcEnv ty11 ty21 of
>     Right theta ->
>       case unifyTypes tcEnv (subst theta ty12) (subst theta ty22) of
>         Right theta' -> Right (compose theta' theta)
>         Left msg -> Left msg
>     Left msg -> Left msg
> unifyTypes tcEnv (TypeArrow ty11 ty12) (TypeArrow ty21 ty22) =
>   case unifyTypes tcEnv ty11 ty21 of
>     Right theta ->
>       case unifyTypes tcEnv (subst theta ty12) (subst theta ty22) of
>         Right theta' -> Right (compose theta' theta)
>         Left msg -> Left msg
>     Left msg -> Left msg
> unifyTypes tcEnv (TypeApply ty11 ty12) (TypeArrow ty21 ty22) =
>   case unifyTypes tcEnv ty11 (TypeApply (TypeConstructor qArrowId) ty21) of
>     Right theta ->
>       case unifyTypes tcEnv (subst theta ty12) (subst theta ty22) of
>         Right theta' -> Right (compose theta' theta)
>         Left msg -> Left msg
>     Left msg -> Left msg
> unifyTypes tcEnv (TypeArrow ty11 ty12) (TypeApply ty21 ty22) =
>   case unifyTypes tcEnv (TypeApply (TypeConstructor qArrowId) ty11) ty21 of
>     Right theta ->
>       case unifyTypes tcEnv (subst theta ty12) (subst theta ty22) of
>         Right theta' -> Right (compose theta' theta)
>         Left msg -> Left msg
>     Left msg -> Left msg
> unifyTypes tcEnv ty1 ty2 = Left (incompatibleTypes tcEnv ty1 ty2)

\end{verbatim}
After performing a unification, the resulting substitution is applied
to the current context and the resulting context is subject to a
context reduction. This context reduction retains all predicates whose
types are simple variables and which are not implied but other
predicates in the context. For all other predicates, the compiler
checks whether an instance exists and replaces them by applying the
instances' contexts to the respective types. A minor complication
arises due to constrained types, which at present are used to
implement overloading of guard expressions and of numeric literals in
patterns. The set of admissible types of a constrained type may be
restricted by the current context after the context reduction and thus
may cause a further extension of the current substitution.
\begin{verbatim}

> reduceContext :: Position -> String -> Doc -> TCEnv -> Context -> a
>               -> TcState (Context,a)
> reduceContext p what doc tcEnv cx x =
>   do
>     iEnv <- liftSt (liftSt envRt)
>     theta <- liftSt fetchSt
>     let cx' = subst theta cx
>         (cx1,cx2) =
>           partitionContext (minContext tcEnv (reduceTypePreds iEnv cx'))
>     theta' <- foldM (reportMissingInstance p what doc tcEnv iEnv) idSubst cx2
>     liftSt (updateSt_ (compose theta'))
>     return (cx1,x)

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
type that must be an instance of \texttt{Num} or one of its
subclasses, the compiler tries to resolve the ambiguity by choosing
the first type from the set $\left\{ \texttt{Int}, \texttt{Float}
\right\}$ that satisfies all constraints for the ambiguous type
variable. An error is reported if no such type exists.

This is similar to Haskell's default rules, except that the user can
specify the set of types used for resolving ambiguous numeric types
with a default declaration in Haskell. Furthermore, in Haskell an
ambiguous type variable $v$ is resolved only if it appears solely in
constraints of the form $C\,v$ and all of these classes are defined in
the Prelude or a standard library (cf.\ Sect.~4.3.4 of the revised
Haskell'98 report~\cite{PeytonJones03:Haskell}).

\ToDo{Support default declarations.}

\ToDo{Adopt Haskell's restrictions?}
\begin{verbatim}

> applyDefaults :: Position -> String -> Doc -> TCEnv -> Set Int -> Context
>               -> Type -> TcState Context
> applyDefaults p what doc tcEnv fvs cx ty =
>   do
>     iEnv <- liftSt (liftSt envRt)
>     let theta =
>           foldr (bindDefault tcEnv iEnv cx) idSubst
>                 (nub [tv | TypePred cls (TypeVariable tv) <- cx,
>                            tv `notElemSet` fvs, isNumClass tcEnv cls])
>         cx' = fst (partitionContext (subst theta cx))
>         ty' = subst theta ty
>         tvs' = nub (filter (`notElemSet` fvs) (concatMap typeVars cx'))
>     unless (null tvs') (errorAt p (ambiguousType what doc tcEnv tvs' cx' ty'))
>     liftSt (updateSt_ (compose theta))
>     return cx'

> bindDefault :: TCEnv -> InstEnv -> [TypePred] -> Int -> TypeSubst -> TypeSubst
> bindDefault tcEnv iEnv cx tv =
>   case foldr (defaultType tcEnv iEnv tv) numTypes cx of
>     [] -> id
>     ty:_ -> bindSubst tv ty

> defaultType :: TCEnv -> InstEnv -> Int -> TypePred -> [Type] -> [Type]
> defaultType tcEnv iEnv tv (TypePred cls (TypeVariable tv'))
>   | tv == tv' = filter (hasInstance iEnv cls)
>   | otherwise = id
> defaultType _ _ _ _ = id

> isNumClass :: TCEnv -> QualIdent -> Bool
> isNumClass tcEnv cls = qNumId `elem` allSuperClasses cls tcEnv

\end{verbatim}
The function \texttt{splitContext} splits a context
$\overline{C_n\,t_n}$ into a pair of contexts
$(\overline{C_{n_1}\,t_{n_1}}, \overline{C_{n_2}\,t_{n_2}})$ such that
all type variables that appear in the types $\overline{t_{n_1}}$ are
elements of a given set of type variables.
\begin{verbatim}

> splitContext :: Set Int -> Context -> (Context,Context)
> splitContext fvs = partition (all (`elemSet` fvs) . typeVars)

\end{verbatim}
For each function declaration, the type checker ensures that no skolem
type escapes its scope. This is slightly more general than the
algorithm in~\cite{LauferOdersky94:AbstractTypes}, which checks for
escaping skolems at every let binding, but is still sound.
\begin{verbatim}

> checkSkolems :: Position -> TCEnv -> Doc -> Set Int -> Context -> Type
>              -> TcState ()
> checkSkolems p tcEnv what fs cx ty =
>   do
>     ty' <- liftM (flip subst ty) (liftSt fetchSt)
>     unless (all (`elemSet` fs) (typeSkolems ty' ++ concatMap typeSkolems cx))
>            (errorAt p (skolemEscapingScope tcEnv what (QualType cx ty')))

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

> freshQualType :: QualIdent -> TcState (Context,Type)
> freshQualType cls =
>   do
>     tv <- freshTypeVar
>     return ([TypePred cls tv],tv)

> freshEnumType, freshNumType, freshFracType :: TcState (Context,Type)
> freshEnumType = freshQualType qEnumId
> freshNumType = freshQualType qNumId
> freshFracType = freshQualType qFractionalId
> freshMonadType = freshQualType qMonadId

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
>   where m = length (snd (unapplyType True (arrowBase ty)))

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
\begin{verbatim}

> isVariablePattern :: ConstrTerm a -> Bool
> isVariablePattern (VariablePattern _ _) = True
> isVariablePattern _ = False

\end{verbatim}
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
> localTypes tyEnv = [ty | (_,Value _ _ ty) <- localBindings tyEnv]

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

> methodSigTooGeneral :: TCEnv -> Doc -> QualType -> TypeScheme -> String
> methodSigTooGeneral tcEnv what ty sigma = show $
>   vcat [text "Method type not general enough", what,
>         text "Inferred type:" <+> ppTypeScheme tcEnv sigma,
>         text "Expected type:" <+> ppQualType tcEnv ty]

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

> skolemEscapingScope :: TCEnv -> Doc -> QualType -> String
> skolemEscapingScope tcEnv what ty = show $
>   vcat [text "Existential type escapes out of its scope", what,
>         text "Type:" <+> ppQualType tcEnv ty]

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

> ambiguousType :: String -> Doc -> TCEnv -> [Int] -> Context -> Type
>               -> String
> ambiguousType what doc tcEnv tvs cx ty = show $
>   vcat [text "Ambiguous type variable" <> plural tvs <+>
>           list (map (ppType tcEnv . TypeVariable) tvs) <+> text "in type",
>         ppQualType tcEnv (canonType (QualType cx ty)),
>         text "inferred for" <+> text what, doc]
>   where plural (_:xs) = if null xs then empty else char 's'
>         list [x] = x
>         list [x1,x2] = x1 <+> text "and" <+> x2
>         list xs = hsep (map (<> comma) (init xs)) <+> text "and" <+> last xs

> noInstance :: String -> Doc -> TCEnv -> QualIdent -> Type -> String
> noInstance what doc tcEnv cls ty = show $
>   vcat [text "Missing" <+> ppInstance tcEnv tp <+> text "instance",
>         text "in" <+> text what,
>         doc]
>   where tp = TypePred cls ty

\end{verbatim}
