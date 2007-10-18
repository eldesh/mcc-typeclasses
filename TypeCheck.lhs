% -*- LaTeX -*-
% $Id: TypeCheck.lhs 2513 2007-10-18 09:50:08Z wlux $
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

The result of type checking is a (flat) top-level environment
containing the types of all constructors, variables, and functions
defined in a program. In addition, a type annotated source module or
goal is returned.
\begin{verbatim}

> module TypeCheck(typeCheck,typeCheckGoal) where
> import Base
> import Combined
> import Curry
> import CurryPP
> import CurryUtils
> import Env
> import Error
> import List
> import Maybe
> import Monad
> import PredefIdent
> import PredefTypes
> import Pretty
> import SCC
> import Set
> import TopEnv
> import Types
> import TypeInfo
> import TypeSubst
> import TypeTrans
> import Utils
> import ValueInfo

> infixl 5 $-$
> infixl 1 >>-, >>=-

> ($-$) :: Doc -> Doc -> Doc
> x $-$ y = x $$ space $$ y

> (>>-) :: Monad m => m (a,b,c) -> (a -> b -> m a) -> m (a,c)
> m >>- f =
>   do
>     (u,x,y) <- m
>     u' <- f u x
>     return (u',y)

> (>>=-) :: Monad m => m (a,b,d) -> (b -> m c) -> m (a,c,d)
> m >>=- f =
>   do
>     (u,x,z) <- m
>     y <- f x
>     return (u,y,z)

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
>       (defaultTypes tcEnv (filter isDefaultDecl tds))
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
>       (defaultTypes tcEnv [])
>       iEnv
>       tyEnv

\end{verbatim}
The type checker makes use of nested state monads in order to maintain
the type environment, the current substitution, the instance
environment and a counter, which is used for generating fresh type
variables.

In order to handle the introduction of local instances when matching a
data constructor with a non-empty right hand side context, the type
checker uses an extended instance environment that is composed of the
static top-level instance environment and a dynamic environment that
maps each class on the instances which are in scope for it. The
rationale behind using this representation is that it makes it easy to
apply the current substitution to the dynamic part of the environment.

For lack of a better place, we also include the list of default types
in the extended instance environment.
\begin{verbatim}

> type TcState a =
>   StateT ValueEnv (StateT TypeSubst (StateT InstEnv' (StateT Int Error))) a
> type InstEnv' = ([Type],Env QualIdent [Type],InstEnv)

> run :: TcState a -> [Type] -> InstEnv -> ValueEnv -> Error a
> run m tys iEnv tyEnv =
>   callSt (callSt (callSt (callSt m tyEnv) idSubst) (tys,emptyEnv,iEnv)) 1

\end{verbatim}
The list of default types is given either by a default declaration in
the source code or defaults to the predefined list of numeric data
types, which at present includes the types \texttt{Int} and
\texttt{Float}. This list is always used when type checking goal
expressions because a goal has no top-level declarations.

\ToDo{Provide a way to set the default types for a goal, e.g. via
  a command line switch.}
\begin{verbatim}

> defaultTypes :: TCEnv -> [TopDecl a] -> [Type]
> defaultTypes _ [] = numTypes
> defaultTypes tcEnv (DefaultDecl _ tys : _) =
>   map (unqualType . expandPolyType tcEnv . QualTypeExpr []) tys

\end{verbatim}
\paragraph{Defining Data Constructors and Methods}
First, the types of all data and newtype constructors as well as those
of all type class methods are entered into the type environment. All
type synonyms occurring in their types are expanded.
\begin{verbatim}

> bindTypeValues :: ModuleIdent -> TCEnv -> TopDecl a -> ValueEnv -> ValueEnv
> bindTypeValues m tcEnv (DataDecl _ cxL tc tvs cs _) tyEnv =
>   foldr bind tyEnv cs
>   where bind (ConstrDecl _ _ cxR c tys) =
>           bindConstr DataConstructor m tcEnv cxL tc tvs cxR c tys
>         bind (ConOpDecl _ _ cxR ty1 op ty2) =
>           bindConstr DataConstructor m tcEnv cxL tc tvs cxR op [ty1,ty2]
> bindTypeValues m tcEnv (NewtypeDecl _ cx tc tvs nc _) tyEnv = bind nc tyEnv
>   where bind (NewConstrDecl _ c ty) =
>           bindConstr (const . const . NewtypeConstructor)
>                      m tcEnv cx tc tvs [] c [ty]
> bindTypeValues _ _ (TypeDecl _ _ _ _) tyEnv = tyEnv
> bindTypeValues m tcEnv (ClassDecl _ _ cls tv ds) tyEnv = foldr bind tyEnv ds
>   where cls' = qualifyWith m cls
>         bind (InfixDecl _ _ _ _) = id
>         bind (TypeSig _ fs ty) = bindMethods m tcEnv cls' tv fs ty
>         bind (FunctionDecl _ _ _) = id
>         bind (TrustAnnot _ _ _) = id
> bindTypeValues _ _ (InstanceDecl _ _ _ _ _) tyEnv = tyEnv
> bindTypeValues _ _ (DefaultDecl _ _) tyEnv = tyEnv
> bindTypeValues _ _ (BlockDecl _) tyEnv = tyEnv

> bindConstr :: (QualIdent -> Int -> ConstrInfo -> TypeScheme -> ValueInfo)
>            -> ModuleIdent -> TCEnv -> [ClassAssert] -> Ident -> [Ident]
>            -> [ClassAssert] -> Ident -> [TypeExpr] -> ValueEnv -> ValueEnv
> bindConstr f m tcEnv cxL tc tvs cxR c tys =
>   globalBindTopEnv m c (f (qualifyWith m c) (length tys) ci (typeScheme ty))
>   where (ci,ty) = expandConstrType tcEnv cxL (qualifyWith m tc) tvs cxR tys

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
performed and the declaration group is split into minimal nested
binding groups which are checked separately. Within each binding
group, first the type environment is extended with new bindings for
all variables and functions defined in the group. Next, types are
inferred for all declarations without an explicit type signature and
the inferred types are then generalized. Finally, the types of all
explicitly typed declarations are checked.

The idea of checking the explicitly typed declarations after the
implicitly typed declarations is due to Mark P.\ Jones' ``Typing
Haskell in Haskell'' paper~\cite{Jones99:THiH}. It has the advantage
of inferring more general types. For instance, given the declarations
\begin{verbatim}
  f :: Eq a => a -> Bool
  f x = (x==x) || g True
  g y = (y<=y) || f True
\end{verbatim}
the compiler will infer type \texttt{Ord a => a -> Bool} for
\texttt{g} if \texttt{f} is checked after inferring a type for
\texttt{g}, but only type \texttt{Bool -> Bool} if both declarations
are checked together.

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

\ToDo{Strictly speaking, numeric literals are not non-expansive since
  they are just abbreviations for the saturated (in fact, over
  applied) applications \texttt{Prelude.fromInt}~$i$ and
  \texttt{Prelude.fromFloat}~$f$, respectively. Therefore, the
  compiler should either consider all numeric literals expansive,
  consider only numeric literals of some predefined types like
  \texttt{Int}, \texttt{Float}, etc. non-expansive, or ensure that all
  \texttt{fromInt} and \texttt{fromFloat} instance method
  implementations are deterministic.}

Note that we do not implement Haskell's monomorphism restriction
(cf.\ Sect.~4.5.5 in~\cite{PeytonJones03:Haskell}), which prevents
generalization of constrained type variables in the types of simple
pattern bindings of the form $x=e$ without an explicit type signature.
The motivation for this restriction is that sharing is lost for an
overloaded declaration, which might cause an expensive computation to
be repeated. However, this argument does not apply to Curry since
generalization is allowed only when $e$ is a non-expansive expression,
i.e., essentially a normal form.

Within a group of mutually recursive declarations, all type variables
that appear in the types of the variables defined in the group and
whose type cannot be generalized must not be generalized in the other
declarations of that group as well. Without this restriction, the
compiler would accept the function
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
>     tyEnv <- fetchSt
>     (cx',impDs') <- mapAccumM (tcDecl m tcEnv tyEnv) cx impDs
>     theta <- liftSt fetchSt
>     let tvs = [tv | (ty,PatternDecl _ t rhs) <- impDs',
>                     not (isVariablePattern t && isNonExpansive tyEnv rhs),
>                     tv <- typeVars (subst theta ty)]
>         fvs = foldr addToSet (fvEnv (subst theta tyEnv0)) tvs
>         (gcx,lcx) = splitContext fvs cx'
>     lcx' <- foldM (uncurry . dfltDecl tcEnv fvs) lcx impDs'
>     theta <- liftSt fetchSt
>     mapM_ (uncurry (genDecl m . gen fvs lcx' . subst theta)) impDs'
>     (cx''',expDs') <-
>       mapAccumM (uncurry . tcCheckDecl m tcEnv tyEnv) gcx expDs
>     return (cx''',map snd impDs' ++ expDs')
>   where (impDs,expDs) = partDecls sigs ds

> partDecls :: SigEnv -> [Decl a] -> ([Decl a],[(QualTypeExpr,Decl a)])
> partDecls sigs =
>   foldr (\d -> maybe (implicit d) (explicit d) (declTypeSig sigs d)) ([],[])
>   where implicit d ~(impDs,expDs) = (d:impDs,expDs)
>         explicit d ty ~(impDs,expDs) = (impDs,(ty,d):expDs)

> declTypeSig :: SigEnv -> Decl a -> Maybe QualTypeExpr
> declTypeSig sigs (FunctionDecl _ f _) = lookupEnv f sigs
> declTypeSig sigs (PatternDecl _ t _) =
>   case t of
>     VariablePattern _ v -> lookupEnv v sigs
>     _ -> Nothing

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

> tcDecl :: ModuleIdent -> TCEnv -> ValueEnv -> Context -> Decl a
>        -> TcState (Context,(Type,Decl Type))
> tcDecl m tcEnv tyEnv0 cx (FunctionDecl p f eqs) =
>   tcFunctionDecl "function" m tcEnv cx (varType f tyEnv0) p f eqs
> tcDecl m tcEnv tyEnv0 cx d@(PatternDecl p t rhs) =
>   do
>     (cx',ty',t') <- tcConstrTerm tcEnv p t
>     (cx'',rhs') <-
>       tcRhs m tcEnv rhs >>-
>       unifyDecl p "pattern declaration" (ppDecl d) tcEnv tyEnv0 (cx++cx') ty'
>     return (cx'',(ty',PatternDecl p t' rhs'))

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
>     cx' <- reduceContext p what' (ppDecl (FunctionDecl p f eqs)) tcEnv
>                          (cx ++ concat cxs)
>     return (cx',(ty',FunctionDecl p f eqs'))
>   where what' = what ++ " declaration"

> tcEquation :: ModuleIdent -> TCEnv -> Set Int -> Type -> Ident -> Equation a
>            -> TcState (Context,Equation Type)
> tcEquation m tcEnv fs ty f eq@(Equation p lhs rhs) =
>   do
>     tyEnv0 <- fetchSt
>     (cx,eq') <-
>       tcEqn m tcEnv p lhs rhs >>-
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
>     (cx,ds') <- tcDecls m tcEnv ds
>     (cx',ty,e') <- tcExpr m tcEnv p e
>     cx'' <- reduceContext p "goal" (ppExpr 0 e) tcEnv (cx ++ cx')
>     checkSkolems p tcEnv (text "Goal:" <+> ppExpr 0 e) zeroSet cx'' ty
>     theta <- liftSt fetchSt
>     let ty' = subst theta ty
>         tvs = if forEval then zeroSet else fromListSet (typeVars ty')
>     cx''' <- applyDefaults p "goal" (ppExpr 0 e) tcEnv tvs cx'' ty'
>     return (cx''',Goal p e' ds')

> unifyDecl :: Position -> String -> Doc -> TCEnv -> ValueEnv -> Context -> Type
>           -> Context -> Type -> TcState Context
> unifyDecl p what doc tcEnv tyEnv0 cxLhs tyLhs cxRhs tyRhs =
>   do
>     cx <- unify p what doc tcEnv tyLhs (cxLhs ++ cxRhs) tyRhs
>     theta <- liftSt fetchSt
>     let ty = subst theta tyLhs
>         fvs = foldr addToSet (fvEnv (subst theta tyEnv0)) (typeVars ty)
>     applyDefaults p what doc tcEnv fvs cx ty

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
type. This is detected in function \texttt{dfltDecl} below, which
fixes the type $\beta_1$ to the default numeric type (\texttt{Int} at
present). Thus, the compiler finally infers types $\forall\alpha .
(\texttt{Num}\,\alpha, \texttt{Ord}\,\alpha) \Rightarrow \alpha
\rightarrow \alpha$ and $\forall\alpha . (\texttt{Num}\,\alpha,
\texttt{Ord}\,\alpha) \Rightarrow \texttt{Int} \rightarrow \alpha
\rightarrow \alpha$ for \texttt{f1} and \texttt{f2}, respectively.

It would be possible to infer more general types for \texttt{f1} and
\texttt{f2} by keeping the (generalized) $\texttt{Num}\,\beta_1$
constraint in \texttt{f1}'s type despite the fact that it is
ambiguous. In fact, this is what ghc, hbc, and nhc98, but not Hugs,
implement. Note that the $\texttt{Num}\,\beta_1$ constraint is not
really ambiguous for the application of \texttt{f1} in \texttt{f2} due
to the fact that recursion is monomorphic without an explicit type
signature and therefore \texttt{f1} and \texttt{f2} must be using the
same instance dictionary for the $\texttt{Num}\,\beta_1$ constraint.
Unfortunately, our dictionary transformation algorithm implemented in
module \texttt{DictTrans} (see Sect.~\ref{sec:dict-trans}) is unable
to make use of this fact.

\ToDo{Change the dictionary transformation algorithm to handle
  ambiguous constraints like $\texttt{Num}\,\beta_1$ above. On the
  side of the type checker, this probably requires that all implicitly
  typed declarations of a declaration group use exactly the same
  context, i.e., contexts must not be sorted during generalization in
  function \texttt{gen} below.}
\begin{verbatim}

> dfltDecl :: TCEnv -> Set Int -> Context -> Type -> Decl Type
>          -> TcState Context
> dfltDecl tcEnv fvs cx ty (FunctionDecl p f _) =
>   applyDefaultsDecl p ("function " ++ name f) tcEnv fvs cx ty
> dfltDecl tcEnv fvs cx ty (PatternDecl p t _) =
>   case t of
>     VariablePattern _ v ->
>       applyDefaultsDecl p ("variable " ++ name v) tcEnv fvs cx ty
>     _ -> return cx

> applyDefaultsDecl :: Position -> String -> TCEnv -> Set Int -> Context -> Type
>                   -> TcState Context
> applyDefaultsDecl p what tcEnv fvs cx ty =
>   do
>     theta <- liftSt fetchSt
>     let ty' = subst theta ty
>         fvs' = foldr addToSet fvs (typeVars ty')
>     applyDefaults p what empty tcEnv fvs' cx ty'

\end{verbatim}
The function \texttt{genDecl} saves the generalized type of a function
or variable declaration without a type signature in the type
environment. The type has been generalized already by
\texttt{tcDeclGroup}.
\begin{verbatim}

> genDecl :: ModuleIdent -> TypeScheme -> Decl a -> TcState ()
> genDecl m ty (FunctionDecl _ f eqs) =
>   updateSt_ (rebindFun m f (eqnArity (head eqs)) ty)
> genDecl m ty (PatternDecl _ t _) =
>   case t of
>     VariablePattern _ v -> updateSt_ (rebindFun m v 0 ty)
>     _ -> return ()

\end{verbatim}
The function \texttt{tcCheckDecl} checks the type of an explicitly
typed function or variable declaration. After inferring a type for the
declaration, the inferred type is compared with the type signature.
Since the inferred type of an explicitly typed function or variable
declaration is automatically an instance of its type signature (cf.\ 
\texttt{tcDecl} above), the type signature is correct only if the
inferred type matches the type signature exactly except for the
inferred context, which may contain only a subset of the declared
context because the context of a function's type signature is
(deliberately) ignored in \texttt{tcFunctionDecl} above.
\begin{verbatim}

> tcCheckDecl :: ModuleIdent -> TCEnv -> ValueEnv -> Context -> QualTypeExpr
>             -> Decl a -> TcState (Context,Decl Type)
> tcCheckDecl m tcEnv tyEnv cx sigTy d =
>   do
>     (cx',(ty,d')) <- tcDecl m tcEnv tyEnv cx d
>     theta <- liftSt fetchSt
>     let fvs = fvEnv (subst theta tyEnv)
>         (gcx,lcx) = splitContext fvs cx'
>         ty' = subst theta ty
>         sigma = if poly then gen fvs lcx ty' else monoType ty'
>     checkDeclSig tcEnv sigTy sigma d'
>     return (gcx,d')
>   where poly = isNonExpansive tyEnv d

> checkDeclSig :: TCEnv -> QualTypeExpr -> TypeScheme -> Decl a -> TcState ()
> checkDeclSig tcEnv sigTy sigma (FunctionDecl p f eqs)
>   | checkTypeSig tcEnv (expandPolyType tcEnv sigTy) sigma = return ()
>   | otherwise = errorAt p (typeSigTooGeneral tcEnv what sigTy sigma)
>   where what = text "Function:" <+> ppIdent f
> checkDeclSig tcEnv sigTy sigma (PatternDecl p t rhs)
>   | checkTypeSig tcEnv (expandPolyType tcEnv sigTy) sigma = return ()
>   | otherwise = errorAt p (typeSigTooGeneral tcEnv what sigTy sigma)
>   where what = text "Variable:" <+> ppConstrTerm 0 t

> checkTypeSig :: TCEnv -> QualType -> TypeScheme -> Bool
> checkTypeSig tcEnv (QualType sigCx sigTy) (ForAll _ (QualType cx ty)) =
>   ty == sigTy && all (`elem` maxContext tcEnv sigCx) cx

> class Binding a where
>   isNonExpansive :: ValueEnv -> a -> Bool

> instance Binding a => Binding [a] where
>   isNonExpansive tyEnv = all (isNonExpansive tyEnv)

> instance Binding (Decl a) where
>   isNonExpansive _ (InfixDecl _ _ _ _) = True
>   isNonExpansive _ (TypeSig _ _ _) = True
>   isNonExpansive _ (FunctionDecl _ _ _) = True
>   isNonExpansive _ (ForeignDecl _ _ _ _ _ _) = True
>   isNonExpansive tyEnv (PatternDecl _ t rhs) =
>     isVariablePattern t && isNonExpansive tyEnv rhs
>   isNonExpansive _ (FreeDecl _ _) = False
>   isNonExpansive _ (TrustAnnot _ _ _) = True

> instance Binding (Rhs a) where
>   isNonExpansive tyEnv (SimpleRhs _ e ds) =
>     isNonExpansive tyEnv ds && isNonExpansive tyEnv e
>   isNonExpansive _ (GuardedRhs _ _) = False

> instance Binding (Expression a) where
>   isNonExpansive tyEnv = isNonExpansiveApp tyEnv 0

> isNonExpansiveApp :: ValueEnv -> Int -> Expression a -> Bool
> isNonExpansiveApp _ _ (Literal _ _) = True
> isNonExpansiveApp tyEnv n (Variable _ v)
>   | isRenamed (unqualify v) = n == 0 || n < arity v tyEnv
>   | otherwise = n < arity v tyEnv
> isNonExpansiveApp _ _ (Constructor _ _) = True
> isNonExpansiveApp tyEnv n (Paren e) = isNonExpansiveApp tyEnv n e
> isNonExpansiveApp tyEnv n (Typed e _) = isNonExpansiveApp tyEnv n e
> isNonExpansiveApp tyEnv _ (Tuple es) = isNonExpansive tyEnv es
> isNonExpansiveApp tyEnv _ (List _ es) = isNonExpansive tyEnv es
> isNonExpansiveApp tyEnv n (Apply f e) =
>   isNonExpansive tyEnv e && isNonExpansiveApp tyEnv (n + 1) f
> isNonExpansiveApp tyEnv n (InfixApply e1 op e2) =
>   isNonExpansiveApp tyEnv (n + 2) (infixOp op) &&
>   isNonExpansive tyEnv e1 && isNonExpansive tyEnv e2
> isNonExpansiveApp tyEnv n (LeftSection e op) =
>   isNonExpansiveApp tyEnv (n + 1) (infixOp op) && isNonExpansive tyEnv e
> isNonExpansiveApp _ n (Lambda _ ts _) = n < length ts
> isNonExpansiveApp tyEnv n (Let ds e) =
>   isNonExpansive tyEnv ds && isNonExpansiveApp tyEnv n e
> isNonExpansiveApp _ _ _ = False

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
>     vds' <- mapM (tcClassMethodDecl m tcEnv (qualify cls) tv sigs) vds
>     return (ClassDecl p cx cls tv (map untyped ods ++ vds'))
>   where sigs = foldr bindTypeSigs noSigs ods
>         (vds,ods) = partition isValueDecl ds
> tcTopDecl m tcEnv (InstanceDecl p cx cls ty ds) =
>   do
>     vds' <- mapM (tcInstMethodDecl m tcEnv cls' ty') vds
>     return (InstanceDecl p cx cls ty (map untyped ods ++ vds'))
>   where cls' = origName (head (qualLookupTopEnv cls tcEnv))
>         ty' = expandPolyType tcEnv (QualTypeExpr cx ty)
>         (vds,ods) = partition isValueDecl ds
> tcTopDecl _ _ (DefaultDecl p tys) = return (DefaultDecl p tys)
> tcTopDecl _ _ (BlockDecl _) = internalError "tcTopDecl"

> tcClassMethodDecl :: ModuleIdent -> TCEnv -> QualIdent -> Ident -> SigEnv
>                   -> Decl a -> TcState (Decl Type)
> tcClassMethodDecl m tcEnv cls tv sigs d =
>   do
>     methTy <- liftM (classMethodType (qualifyWith m) d) fetchSt
>     (ty',d') <- tcMethodDecl m tcEnv methTy d
>     checkClassMethodType tcEnv (clsType cls tv (classMethodSig sigs d)) ty' d'
>     return d'
>   where clsType cls tv (QualTypeExpr cx ty) =
>           QualTypeExpr (ClassAssert cls (VariableType tv) : cx) ty

> checkClassMethodType :: TCEnv -> QualTypeExpr -> TypeScheme -> Decl Type
>                      -> TcState ()
> checkClassMethodType tcEnv sigTy sigma (FunctionDecl p f _)
>   | checkTypeSig tcEnv (expandPolyType tcEnv sigTy) sigma = return ()
>   | otherwise = errorAt p (typeSigTooGeneral tcEnv what sigTy sigma)
>   where what = text "Method:" <+> ppIdent f

> tcInstMethodDecl :: ModuleIdent -> TCEnv -> QualIdent -> QualType -> Decl a
>                  -> TcState (Decl Type)
> tcInstMethodDecl m tcEnv cls instTy d =
>   do
>     methTy <- liftM (instMethodType (qualifyLike cls) instTy d) fetchSt
>     (ty',d') <- tcMethodDecl m tcEnv (typeScheme methTy) d
>     checkInstMethodType tcEnv (normalize 0 methTy) ty' d'
>     return d'

> checkInstMethodType :: TCEnv -> QualType -> TypeScheme -> Decl Type
>                     -> TcState ()
> checkInstMethodType tcEnv methTy sigma (FunctionDecl p f _)
>   | checkTypeSig tcEnv methTy sigma = return ()
>   | otherwise = errorAt p (methodSigTooGeneral tcEnv what methTy sigma)
>   where what = text "Method:" <+> ppIdent f

> tcMethodDecl :: ModuleIdent -> TCEnv -> TypeScheme -> Decl a
>              -> TcState (TypeScheme,Decl Type)
> tcMethodDecl m tcEnv methTy (FunctionDecl p f eqs) =
>   do
>     updateSt_ (bindFun m f (eqnArity (head eqs)) methTy)
>     (cx,(ty,d')) <- tcFunctionDecl "method" m tcEnv [] methTy p f eqs
>     theta <- liftSt fetchSt
>     return (gen zeroSet cx (subst theta ty),d')

> classMethodSig :: SigEnv -> Decl a -> QualTypeExpr
> classMethodSig sigs (FunctionDecl _ f _) =
>   fromJust (lookupEnv (unRenameIdent f) sigs)

> classMethodType :: (Ident -> QualIdent) -> Decl a -> ValueEnv -> TypeScheme
> classMethodType qualify (FunctionDecl _ f _) tyEnv =
>   funType (qualify (unRenameIdent f)) tyEnv

> instMethodType :: (Ident -> QualIdent) -> QualType -> Decl a -> ValueEnv
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
regard to marshaling). The type of a dynamic function wrapper is
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
>     checkForeignType cc (unqualType ty')
>     updateSt_ (bindFun m f (foreignArity (unqualType ty')) (typeScheme ty'))
>   where ty' = expandPolyType tcEnv (QualTypeExpr [] ty)
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
Note that the type attribute associated with a constructor or infix
pattern is the type of the whole pattern and not the type of the
constructor itself. Also note that overloaded literals are not
supported in patterns.

\ToDo{The types admissible for numeric literals in patterns should
  in some way acknowledge the set of types specified in a default
  declaration if one is present.}

When computing the type of a variable in a pattern, we ignore the
context of the variable's type (which can only be due to a type
signature in the same declaration group) for just the same reason as
in \texttt{tcFunctionDecl} above.
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
>     (_,ty) <- fetchSt >>= inst . varType v
>     return ([],ty,VariablePattern ty v)
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
>           tcConstrTerm tcEnv p t >>-
>           unify p "pattern" (doc $-$ text "Term:" <+> ppConstrTerm 0 t)
>                 tcEnv ty
> tcConstrTerm tcEnv p t@(AsPattern v t') =
>   do
>     (_,ty) <- fetchSt >>= inst . varType v
>     (cx,t'') <-
>       tcConstrTerm tcEnv p t' >>-
>       unify p "pattern" (ppConstrTerm 0 t) tcEnv ty
>     return (cx,ty,AsPattern v t'')
> tcConstrTerm tcEnv p (LazyPattern t) =
>   do
>     (cx,ty,t') <- tcConstrTerm tcEnv p t
>     return (cx,ty,LazyPattern t')

> tcConstrApp :: TCEnv -> Position -> Doc -> QualIdent -> [ConstrTerm a]
>             -> TcState (Context,Type,[ConstrTerm Type])
> tcConstrApp tcEnv p doc c ts =
>   do
>     tyEnv <- fetchSt
>     (cx,(tys,ty)) <- liftM (apSnd arrowUnapply) (skol tcEnv (conType c tyEnv))
>     unless (length tys == n) (errorAt p (wrongArity c (length tys) n))
>     (cxs,ts') <- liftM unzip $ zipWithM (tcConstrArg tcEnv p doc) ts tys
>     return (cx ++ concat cxs,ty,ts')
>   where n = length ts

> tcConstrArg :: TCEnv -> Position -> Doc -> ConstrTerm a -> Type
>             -> TcState (Context,ConstrTerm Type)
> tcConstrArg tcEnv p doc t ty =
>   tcConstrTerm tcEnv p t >>-
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
>     (cx,g') <- tcExpr m tcEnv p g >>- unify p "guard" (ppExpr 0 g) tcEnv gty
>     (cx',e') <-
>       tcExpr m tcEnv p e >>-
>       unify p "guarded expression" (ppExpr 0 e) tcEnv ty
>     return (cx ++ cx',CondExpr p g' e')

> tcExpr :: ModuleIdent -> TCEnv -> Position -> Expression a
>        -> TcState (Context,Type,Expression Type)
> tcExpr _ _ _ (Literal _ l) =
>   do
>     (cx,ty) <- tcLiteral True l
>     return (cx,ty,Literal ty l)
> tcExpr _ _ _ (Variable _ v) =
>   do
>     (cx,ty) <- fetchSt >>= inst . funType v
>     return (cx,ty,Variable ty v)
> tcExpr _ _ _ (Constructor _ c) =
>   do
>     (cx,ty) <- fetchSt >>= inst . snd . conType c
>     return (cx,ty,Constructor ty c)
> tcExpr m tcEnv p (Typed e sig) =
>   do
>     tyEnv0 <- fetchSt
>     (cx,ty) <- inst (typeScheme sigTy)
>     (cx',e') <-
>       tcExpr m tcEnv p e >>-
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
>           tcExpr m tcEnv p e >>-
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
>       tcExpr m tcEnv p e1 >>-
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) tcEnv ty
>     return (cx ++ cx',listType ty,EnumFrom e1')
> tcExpr m tcEnv p e@(EnumFromThen e1 e2) =
>   do
>     (cx,ty) <- freshEnumType
>     (cx',e1') <-
>       tcExpr m tcEnv p e1 >>-
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) tcEnv ty
>     (cx'',e2') <-
>       tcExpr m tcEnv p e2 >>-
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) tcEnv ty
>     return (cx ++ cx' ++ cx'',listType ty,EnumFromThen e1' e2')
> tcExpr m tcEnv p e@(EnumFromTo e1 e2) =
>   do
>     (cx,ty) <- freshEnumType
>     (cx',e1') <-
>       tcExpr m tcEnv p e1 >>-
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) tcEnv ty
>     (cx'',e2') <-
>       tcExpr m tcEnv p e2 >>-
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) tcEnv ty
>     return (cx ++ cx' ++ cx'',listType ty,EnumFromTo e1' e2')
> tcExpr m tcEnv p e@(EnumFromThenTo e1 e2 e3) =
>   do
>     (cx,ty) <- freshEnumType
>     (cx',e1') <-
>       tcExpr m tcEnv p e1 >>-
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) tcEnv ty
>     (cx'',e2') <-
>       tcExpr m tcEnv p e2 >>-
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) tcEnv ty
>     (cx''',e3') <-
>       tcExpr m tcEnv p e3 >>-
>       unify p "arithmetic sequence"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e3) tcEnv ty
>     return (cx ++ cx' ++ cx'' ++ cx''',listType ty,EnumFromThenTo e1' e2' e3')
> tcExpr m tcEnv p e@(UnaryMinus e1) =
>   do
>     (cx,ty) <- freshNumType
>     (cx',e1') <-
>       tcExpr m tcEnv p e1 >>-
>       unify p "unary negation" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             tcEnv ty
>     return (cx ++ cx',ty,UnaryMinus e1')
> tcExpr m tcEnv p e@(Apply e1 e2) =
>   do
>     (cx,(alpha,beta),e1') <-
>       tcExpr m tcEnv p e1 >>=-
>       tcArrow p "application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>               tcEnv
>     (cx',e2') <-
>       tcExpr m tcEnv p e2 >>-
>       unify p "application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2)
>             tcEnv alpha
>     return (cx ++ cx',beta,Apply e1' e2')
> tcExpr m tcEnv p e@(InfixApply e1 op e2) =
>   do
>     (cx,(alpha,beta,gamma),op') <-
>       tcInfixOp m tcEnv p op >>=-
>       tcBinary p "infix application"
>                (ppExpr 0 e $-$ text "Operator:" <+> ppOp op) tcEnv
>     (cx',e1') <-
>       tcExpr m tcEnv p e1 >>-
>       unify p "infix application"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1) tcEnv alpha
>     (cx'',e2') <-
>       tcExpr m tcEnv p e2 >>-
>       unify p "infix application"
>             (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e2) tcEnv beta
>     return (cx ++ cx' ++ cx'',gamma,InfixApply e1' op' e2')
> tcExpr m tcEnv p e@(LeftSection e1 op) =
>   do
>     (cx,(alpha,beta),op') <-
>       tcInfixOp m tcEnv p op >>=-
>       tcArrow p "left section" (ppExpr 0 e $-$ text "Operator:" <+> ppOp op)
>               tcEnv
>     (cx',e1') <-
>       tcExpr m tcEnv p e1 >>-
>       unify p "left section" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             tcEnv alpha
>     return (cx ++ cx',beta,LeftSection e1' op')
> tcExpr m tcEnv p e@(RightSection op e1) =
>   do
>     (cx,(alpha,beta,gamma),op') <-
>       tcInfixOp m tcEnv p op >>=-
>       tcBinary p "right section"
>                (ppExpr 0 e $-$ text "Operator:" <+> ppOp op) tcEnv
>     (cx',e1') <-
>       tcExpr m tcEnv p e1 >>-
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
>       tcExpr m tcEnv p e >>- unify p "statement" (ppExpr 0 e) tcEnv ty
>     return (cx ++ concat cxs ++ cx',ty,Do sts' e')
> tcExpr m tcEnv p e@(IfThenElse e1 e2 e3) =
>   do
>     (cx,e1') <-
>       tcExpr m tcEnv p e1 >>-
>       unify p "expression" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>             tcEnv boolType
>     (cx',ty,e2') <- tcExpr m tcEnv p e2
>     (cx'',e3') <-
>       tcExpr m tcEnv p e3 >>-
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
>       tcConstrTerm tcEnv p t >>-
>       unify p "case pattern" (doc $-$ text "Term:" <+> ppConstrTerm 0 t)
>             tcEnv tyLhs
>     (cx',rhs') <- tcRhs m tcEnv rhs >>- unify p "case branch" doc tcEnv tyRhs
>     return (cx ++ cx',Alt p t' rhs')
>   where doc = ppAlt a

> tcQual :: ModuleIdent -> TCEnv -> Position -> Statement a
>        -> TcState (Context,Statement Type)
> tcQual m tcEnv p (StmtExpr e) =
>   do
>     (cx,e') <-
>       tcExpr m tcEnv p e >>- unify p "guard" (ppExpr 0 e) tcEnv boolType
>     return (cx,StmtExpr e')
> tcQual m tcEnv _ q@(StmtBind p t e) =
>   do
>     bindLambdaVars m t
>     (cx,ty,t') <- tcConstrTerm tcEnv p t
>     (cx',e') <-
>       tcExpr m tcEnv p e >>-
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
>       tcExpr m tcEnv p e >>-
>       unify p "statement" (ppExpr 0 e) tcEnv (TypeApply mTy alpha)
>     return (cx',StmtExpr e')
> tcStmt m tcEnv _ mTy st@(StmtBind p t e) =
>   do
>     bindLambdaVars m t
>     (cx,ty,t') <- tcConstrTerm tcEnv p t
>     (cx',e') <-
>       tcExpr m tcEnv p e >>-
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

> tcArrow :: Position -> String -> Doc -> TCEnv -> Type -> TcState (Type,Type)
> tcArrow p what doc tcEnv ty =
>   do
>     theta <- liftSt fetchSt
>     unaryArrow (subst theta ty)
>   where unaryArrow (TypeArrow ty1 ty2) = return (ty1,ty2)
>         unaryArrow (TypeVariable tv) =
>           do
>             alpha <- freshTypeVar
>             beta <- freshTypeVar
>             liftSt (updateSt_ (bindVar tv (TypeArrow alpha beta)))
>             return (alpha,beta)
>         unaryArrow ty = errorAt p (nonFunctionType what doc tcEnv ty)

> tcBinary :: Position -> String -> Doc -> TCEnv -> Type
>          -> TcState (Type,Type,Type)
> tcBinary p what doc tcEnv ty = tcArrow p what doc tcEnv ty >>= binaryArrow
>   where binaryArrow (ty1,TypeArrow ty2 ty3) = return (ty1,ty2,ty3)
>         binaryArrow (ty1,TypeVariable tv) =
>           do
>             beta <- freshTypeVar
>             gamma <- freshTypeVar
>             liftSt (updateSt_ (bindVar tv (TypeArrow beta gamma)))
>             return (ty1,beta,gamma)
>         binaryArrow (ty1,ty2) =
>           errorAt p (nonBinaryOp what doc tcEnv (TypeArrow ty1 ty2))

\end{verbatim}
\paragraph{Unification}
The unification uses Robinson's algorithm (cf., e.g., Chap.~9
of~\cite{PeytonJones87:Book}).
\begin{verbatim}

> unify :: Position -> String -> Doc -> TCEnv -> Type -> Context -> Type
>       -> TcState Context
> unify p what doc tcEnv ty1 cx ty2 =
>   do
>     theta <- liftSt fetchSt
>     let ty1' = subst theta ty1
>     let ty2' = subst theta ty2
>     either (errorAt p . typeMismatch what doc tcEnv ty1' ty2')
>            (liftSt . updateSt_ . compose)
>            (unifyTypes tcEnv ty1' ty2')
>     reduceContext p what doc tcEnv cx

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

> reduceContext :: Position -> String -> Doc -> TCEnv -> Context
>               -> TcState Context
> reduceContext p what doc tcEnv cx =
>   do
>     theta <- liftSt fetchSt
>     iEnv <- liftM (apSnd3 (fmap (subst theta))) (liftSt (liftSt fetchSt))
>     let cx' = subst theta cx
>         (cx1,cx2) =
>           partitionContext (minContext tcEnv (reduceTypePreds iEnv cx'))
>     theta' <- foldM (reportMissingInstance p what doc tcEnv iEnv) idSubst cx2
>     liftSt (updateSt_ (compose theta'))
>     return cx1

> reduceTypePreds :: InstEnv' -> Context -> Context
> reduceTypePreds iEnv = concatMap (reduceTypePred iEnv)

> reduceTypePred :: InstEnv' -> TypePred -> Context
> reduceTypePred iEnv (TypePred cls ty) =
>   maybe [TypePred cls ty] (reduceTypePreds iEnv) (instContext iEnv cls ty)

> instContext :: InstEnv' -> QualIdent -> Type -> Maybe Context
> instContext (_,dEnv,iEnv) cls ty =
>   case lookupEnv cls dEnv of
>     Just tys | ty `elem` tys -> Just []
>     _ ->
>       case unapplyType False ty of
>         (TypeConstructor tc,tys) ->
>           fmap (map (expandAliasType tys) . snd) (lookupEnv (CT cls tc) iEnv)
>         _ -> Nothing

> partitionContext :: Context -> (Context,Context)
> partitionContext cx = partition (\(TypePred _ ty) -> isTypeVar ty) cx
>   where isTypeVar (TypeConstructor _) = False
>         isTypeVar (TypeVariable _) = True
>         isTypeVar (TypeConstrained _ _) = False
>         isTypeVar (TypeSkolem _) = False
>         isTypeVar (TypeApply ty _) = isTypeVar ty
>         isTypeVar (TypeArrow _ _) = False

> reportMissingInstance :: Position -> String -> Doc -> TCEnv -> InstEnv'
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

> hasInstance :: InstEnv' -> QualIdent -> Type -> Bool
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
the first type from the list of default types that satisfies all
constraints for the ambiguous type variable. An error is reported if
no such type exists.

At present, we do not implement two restrictions mandated by the
revised Haskell'98 report~\cite{PeytonJones03:Haskell} (cf.\ 
Sect.~4.3.4). In particular, in Haskell an ambiguous type variable $v$
is resolved only if it appears only in constraints of the form $C\,v$
and all of these classes are defined in the Prelude or a standard
library.

\ToDo{Adopt Haskell's restrictions?}
\begin{verbatim}

> applyDefaults :: Position -> String -> Doc -> TCEnv -> Set Int -> Context
>               -> Type -> TcState Context
> applyDefaults p what doc tcEnv fvs cx ty =
>   do
>     iEnv <- liftSt (liftSt fetchSt)
>     let theta =
>           foldr (bindDefault tcEnv iEnv cx) idSubst
>                 (nub [tv | TypePred cls (TypeVariable tv) <- cx,
>                            tv `notElemSet` fvs, isNumClass tcEnv cls])
>         cx' = fst (partitionContext (subst theta cx))
>         ty' = subst theta ty
>         tvs' = nub (filter (`notElemSet` fvs) (typeVars cx'))
>     unless (null tvs') (errorAt p (ambiguousType what doc tcEnv tvs' cx' ty'))
>     liftSt (updateSt_ (compose theta))
>     return cx'

> bindDefault :: TCEnv -> InstEnv' -> [TypePred] -> Int -> TypeSubst
>                      -> TypeSubst
> bindDefault tcEnv iEnv cx tv =
>   case foldr (defaultType tcEnv iEnv tv) (fst3 iEnv) cx of
>     [] -> id
>     ty:_ -> bindSubst tv ty

> defaultType :: TCEnv -> InstEnv' -> Int -> TypePred -> [Type] -> [Type]
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
>     ty' <- liftM (QualType cx . flip subst ty) (liftSt fetchSt)
>     unless (all (`elemSet` fs) (typeSkolems ty'))
>            (errorAt p (skolemEscapingScope tcEnv what ty'))

\end{verbatim}
\paragraph{Instantiation and Generalization}
We use negative offsets for fresh type variables.
\begin{verbatim}

> fresh :: (Int -> a) -> TcState a
> fresh f = liftM f (liftSt (liftSt (liftSt (updateSt (1 +)))))

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
All constraints that appear on the right hand side of the
constructor's declaration are added to the dynamic instance
environment.
\begin{verbatim}

> skol :: TCEnv -> (ConstrInfo,TypeScheme) -> TcState (Context,Type)
> skol tcEnv (ConstrInfo m cxR,ForAll n (QualType cx ty)) =
>   do
>     tys <- replicateM (n - m) freshTypeVar
>     tys' <- replicateM m freshSkolem
>     let tys'' = tys ++ tys'
>     liftSt (liftSt (updateSt_ (apSnd3 (bindSkolemInsts tys''))))
>     return (map (expandAliasType tys) cxL,expandAliasType tys'' ty)
>   where cxL = filter (`notElem` cxR) cx
>         bindSkolemInsts tys dEnv =
>           foldr bindSkolemInst dEnv
>                 (map (expandAliasType tys) (maxContext tcEnv cxR))
>         bindSkolemInst (TypePred cls ty) dEnv =
>           bindEnv cls (ty : fromMaybe [] (lookupEnv cls dEnv)) dEnv

\end{verbatim}
The function \texttt{gen} generalizes a context \emph{cx} and a type
$\tau$ into a type scheme $\forall\overline{\alpha} . \emph{cx}
\Rightarrow \tau$ by universally quantifying all type variables that
are free in $\tau$ and not fixed by the environment. The set of the
latter is given by \texttt{gen}'s first argument.
\begin{verbatim}

> gen :: Set Int -> Context -> Type -> TypeScheme
> gen fvs cx ty = ForAll (length tvs) (canonType (subst theta (QualType cx ty)))
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
> fvEnv tyEnv = fromListSet (typeVars (localTypes tyEnv))

> fsEnv :: ValueEnv -> Set Int
> fsEnv tyEnv = fromListSet (typeSkolems (localTypes tyEnv))

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
