% -*- LaTeX -*-
% $Id: TypeCheck.lhs 3229 2016-06-16 09:08:31Z wlux $
%
% Copyright (c) 1999-2015, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{TypeCheck.lhs}
\section{Type Inference}
This module implements the type checker of the Curry compiler. The
type checker is invoked after the syntactic correctness of the program
has been verified and kind checking has been applied to all type
expressions. Local variables have been renamed already. Therefore, the
compiler can maintain a flat type environment. The type checker now
checks the correct typing of all expressions and also verifies that
the type signatures given by the user match the inferred types. The
type checker uses algorithm W~\cite{DamasMilner82:Principal} for
inferring the types of unannotated declarations, but allows for
polymorphic recursion when a type annotation is present.

The result of type checking is a (flat) top-level environment
containing the types of all constructors, variables, and functions
defined at the top level of a module. In addition, a type annotated
source module or goal is returned. Note that type annotations on the
left hand side of a declaration hold the function or variable's
generalized type with the type scheme's for all qualifier left
implicit. Type annotations on the right hand side of a declaration
hold the particular instance at which a polymorphic function or
variable is used.
\begin{verbatim}

> module TypeCheck(typeCheck,typeCheckGoal) where
> import Applicative hiding(empty)
> import Base
> import Combined
> import Curry
> import CurryPP
> import CurryUtils
> import Env
> import Error
> import InstInfo
> import List
> import Maybe
> import Monad
> import Position
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
>           -> Error (ValueEnv,[TopDecl QualType])
> typeCheck m tcEnv iEnv tyEnv ds =
>   sequenceA [tcDataDecl tcEnv tvs cs | DataDecl _ _ _ tvs cs _ <- tds] >>
>   run (do
>          mapM_ (defaultTypes tcEnv) (filter isDefaultDecl tds)
>          (tyEnv'',cx,vds') <- tcDecls m tcEnv tyEnv' [d | BlockDecl d <- vds]
>          unless (null cx) (internalError ("typeCheck " ++ show cx))
>          tds' <- mapM (tcTopDecl m tcEnv tyEnv'') tds
>          theta <- fetchSt
>          return (subst theta tyEnv'',
>                  map (fmap (subst theta)) (tds' ++ map BlockDecl vds')))
>       iEnv
>   where (vds,tds) = partition isBlockDecl ds
>         tyEnv' = foldr (bindTypeValues m tcEnv) tyEnv tds

\end{verbatim}
Type checking of a goal is simpler because there are no type
declarations. Depending on whether we only compute the type of a goal
or a going to generate code for the goal, the compiler will allow a
non-empty context for the goal's type or not.
\begin{verbatim}

> typeCheckGoal :: Bool -> ModuleIdent -> TCEnv -> InstEnv -> ValueEnv -> Goal a
>               -> Error (Context,Goal QualType)
> typeCheckGoal forEval m tcEnv iEnv tyEnv g =
>   run (do
>          (cx',g') <-
>            tcGoal m tcEnv tyEnv g >>= uncurry3 (defaultGoalType forEval tcEnv)
>          theta <- fetchSt
>          return (cx',fmap (subst theta) g'))
>       iEnv

> defaultGoalType :: Bool -> TCEnv -> Context -> Type -> Goal a
>                 -> TcState (Context,Goal a)
> defaultGoalType forEval tcEnv cx ty (Goal p e ds) =
>   do
>     theta <- fetchSt
>     let ty' = subst theta ty
>         tvs = if forEval then zeroSet else fromListSet (typeVars ty')
>     cx' <- applyDefaults p "goal" (ppExpr 0 e) tcEnv tvs cx ty'
>     return (cx',Goal p e ds)

\end{verbatim}
The type checker makes use of nested state monads in order to maintain
the current substitution, the instance environment, and a counter,
which is used for generating fresh type variables.

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

> type TcState a = StateT TypeSubst (StateT InstEnv' (StateT Int Error)) a
> type InstEnv' = ([Type],Env QualIdent [Type],InstEnv)

> run :: TcState a -> InstEnv -> Error a
> run m iEnv =
>   callSt (callSt (callSt m idSubst) (defaultDefaultTypes,emptyEnv,iEnv)) 1

\end{verbatim}
The list of default types is given either by a default declaration in
the source code or defaults to the predefined list of numeric data
types, which at present includes the types \texttt{Integer} and
\texttt{Float}. This list is always used when type checking goal
expressions because a goal has no top-level declarations.

Note that it is possible to declare polymorphic default types, e.g.,
\texttt{default (T a)}. Since defaults are used only to disambiguate
ambiguous type variables, i.e., type variables which the type
inference algorithm cannot constrain to a more specific type, it is
safe to use a single instance of a polymorphic default type for the
whole module.

\ToDo{Provide a way to set the default types for a goal, e.g. via
  a command line switch.}
\begin{verbatim}

> defaultTypes :: TCEnv -> TopDecl a -> TcState ()
> defaultTypes tcEnv (DefaultDecl _ tys) =
>   do
>     tys' <- mapM (liftM snd . inst . typeScheme . defaultType) tys
>     liftSt (updateSt_ (apFst3 (const tys')))
>   where defaultType = expandPolyType tcEnv . QualTypeExpr []

> defaultDefaultTypes :: [Type]
> defaultDefaultTypes = [integerType,floatType]

\end{verbatim}
\paragraph{Defining Data Constructors and Methods}
First, the types of all data and newtype constructors as well as those
of their field labels and the types of all type class methods are
entered into the type environment. All type synonyms occurring in
their types are expanded.
\begin{verbatim}

> bindTypeValues :: ModuleIdent -> TCEnv -> TopDecl a -> ValueEnv -> ValueEnv
> bindTypeValues m tcEnv (DataDecl _ cxL tc tvs cs _) tyEnv =
>   foldr bindCon (foldr (uncurry bindLab) tyEnv (nubBy sameLabel ls)) cs
>   where ls = [(l,ty) | RecordDecl _ _ _ _ fs <- cs,
>                        FieldDecl _ ls ty <- fs, l <- ls]
>         bindCon (ConstrDecl _ _ cxR c tys) =
>           bindConstr m tcEnv cxL tc tvs cxR c (zip (repeat anonId) tys)
>         bindCon (ConOpDecl _ _ cxR ty1 op ty2) =
>           bindConstr m tcEnv cxL tc tvs cxR op [(anonId,ty1),(anonId,ty2)]
>         bindCon (RecordDecl _ _ cxR c fs) =
>           bindConstr m tcEnv cxL tc tvs cxR c tys
>           where tys = [(l,ty) | FieldDecl _ ls ty <- fs, l <- ls]
>         bindLab = bindLabel m tcEnv cxL tc tvs
>         sameLabel (l1,_) (l2,_) = l1 == l2
> bindTypeValues m tcEnv (NewtypeDecl _ cx tc tvs nc _) tyEnv = bind nc tyEnv
>   where bind (NewConstrDecl _ c ty) =
>           bindNewConstr m tcEnv cx tc tvs c anonId ty
>         bind (NewRecordDecl _ c l ty) =
>           bindNewConstr m tcEnv cx tc tvs c l ty .
>           bindLabel m tcEnv cx tc tvs l ty
> bindTypeValues _ _ (TypeDecl _ _ _ _) tyEnv = tyEnv
> bindTypeValues m tcEnv (ClassDecl _ _ cls tv ds) tyEnv = foldr bind tyEnv ds
>   where cls' = qualifyWith m cls
>         bind (InfixDecl _ _ _ _) = id
>         bind (TypeSig _ fs ty) = bindMethods m tcEnv cls' tv fs ty
>         bind (FunctionDecl _ _ _ _) = id
>         bind (TrustAnnot _ _ _) = id
> bindTypeValues _ _ (InstanceDecl _ _ _ _ _) tyEnv = tyEnv
> bindTypeValues _ _ (DefaultDecl _ _) tyEnv = tyEnv
> bindTypeValues _ _ (BlockDecl _) tyEnv = tyEnv

> bindConstr :: ModuleIdent -> TCEnv -> [ClassAssert] -> Ident -> [Ident]
>            -> [ClassAssert] -> Ident -> [(Ident,TypeExpr)] -> ValueEnv
>            -> ValueEnv
> bindConstr m tcEnv cxL tc tvs cxR c tys = globalBindTopEnv m c $
>   DataConstructor (qualifyWith m c) ls ci (typeScheme ty)
>   where (ci,ty) = expandConstrType tcEnv cxL (qualifyWith m tc) tvs cxR tys'
>         (ls,tys') = unzip tys

> bindNewConstr :: ModuleIdent -> TCEnv -> [ClassAssert] -> Ident -> [Ident]
>               -> Ident -> Ident -> TypeExpr -> ValueEnv -> ValueEnv
> bindNewConstr m tcEnv cx tc tvs c l ty = globalBindTopEnv m c $
>   NewtypeConstructor (qualifyWith m c) l (typeScheme ty')
>   where ty' = snd (expandConstrType tcEnv cx (qualifyWith m tc) tvs [] [ty])

> bindLabel :: ModuleIdent -> TCEnv -> [ClassAssert] -> Ident -> [Ident]
>           -> Ident -> TypeExpr -> ValueEnv -> ValueEnv
> bindLabel m tcEnv cx tc tvs l ty =
>   globalBindTopEnv m l (Value (qualifyWith m l) 1 (typeScheme ty'))
>   where ty' = expandPolyType tcEnv (QualTypeExpr cx (ArrowType ty0 ty))
>         ty0 = constrType (qualifyWith m tc) tvs

> bindMethods :: ModuleIdent -> TCEnv -> QualIdent -> Ident -> [Ident]
>             -> QualTypeExpr -> ValueEnv -> ValueEnv
> bindMethods m tcEnv cls tv fs ty tyEnv =
>   foldr (bindMethod m (typeScheme ty')) tyEnv fs
>   where ty' = expandMethodType tcEnv cls tv ty

> bindMethod :: ModuleIdent -> TypeScheme -> Ident -> ValueEnv -> ValueEnv
> bindMethod m ty f = globalBindTopEnv m f (Value (qualifyWith m f) 0 ty)

> constrType :: QualIdent -> [Ident] -> TypeExpr
> constrType tc tvs =
>   foldl ApplyType (ConstructorType tc) (map VariableType tvs)

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
\paragraph{Top-level Declarations}
When a field label occurs in more than one constructor declaration of
a data type, the compiler ensures that the label is defined
consistently. In addition, the compiler ensures that no existentially
quantified type variable occurs in the type of a field label because
such type variables necessarily escape their scope with the type of
the record selection function associated with the field label.
\begin{verbatim}

> tcDataDecl :: TCEnv -> [Ident] -> [ConstrDecl] -> Error ()
> tcDataDecl tcEnv tvs cs =
>   mapA (uncurry (tcFieldLabel tcEnv tvs)) ls >>=
>   mapA_ (uncurry tcFieldLabels) . groupLabels
>   where ls = [(P p l,ty) | RecordDecl _ _ _ _ fs <- cs,
>                            FieldDecl p ls ty <- fs, l <- ls]

> tcFieldLabel :: TCEnv -> [Ident] -> P Ident -> TypeExpr
>              -> Error (P Ident,QualType)
> tcFieldLabel tcEnv tvs (P p l) ty
>   | n <= length tvs = return (P p l,ty')
>   | otherwise = errorAt p (skolemFieldLabel l)
>   where ForAll n ty' = polyType (expandMonoType tcEnv tvs ty)

> tcFieldLabels :: P Ident -> [QualType] -> Error ()
> tcFieldLabels (P p l) (ty:tys) =
>   unless (all (ty ==) tys) (errorAt p (inconsistentFieldLabel l))

> groupLabels :: Eq a => [(a,b)] -> [(a,[b])]
> groupLabels [] = []
> groupLabels ((x,y):xys) = (x,y:map snd xys') : groupLabels xys''
>   where (xys',xys'') = partition ((x ==) . fst) xys

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

> tcDecls :: ModuleIdent -> TCEnv -> ValueEnv -> [Decl a]
>         -> TcState (ValueEnv,Context,[Decl QualType])
> tcDecls m tcEnv tyEnv ds =
>   do
>     ((tyEnv',cx),dss') <-
>       mapAccumM (uncurry (tcDeclGroup m tcEnv sigs)) (tyEnv,[])
>                 (scc bv (qfv m) vds)
>     return (tyEnv',cx,map untyped ods ++ concat dss')
>   where (vds,ods) = partition isValueDecl ds
>         sigs = foldr bindTypeSigs noSigs ods

> tcDeclGroup :: ModuleIdent -> TCEnv -> SigEnv -> ValueEnv -> Context
>             -> [Decl a] -> TcState ((ValueEnv,Context),[Decl QualType])
> tcDeclGroup m tcEnv _ tyEnv cx [ForeignDecl p fi _ f ty] =
>   do
>     (tyEnv',ty') <- tcForeignFunct m tcEnv tyEnv p fi f ty
>     return ((tyEnv',cx),[ForeignDecl p fi (qualType ty') f ty])
> tcDeclGroup m tcEnv sigs tyEnv cx [FreeDecl p vs] =
>   do
>     vs' <- mapM (tcDeclVar False tcEnv sigs p) (bv vs)
>     return ((bindVars m tyEnv vs',cx),[FreeDecl p (map freeVar vs')])
>   where freeVar (v,_,ForAll _ ty) = FreeVar ty v
> tcDeclGroup m tcEnv sigs tyEnv cx ds =
>   do
>     vss <- mapM (tcDeclVars tcEnv sigs) ds
>     let tyEnv' = bindVars m tyEnv (concat vss)
>     (cx',impDs') <- mapAccumM (tcDecl m tcEnv tyEnv') cx impDs
>     theta <- fetchSt
>     let tvs =
>           [tv | (ty,d) <- impDs', not (isNonExpansive tcEnv tyEnv' d),
>                 tv <- typeVars (subst theta ty)]
>         fvs = foldr addToSet (fvEnv (subst theta tyEnv)) tvs
>         (gcx,lcx) = splitContext fvs cx'
>     lcx' <- foldM (uncurry . dfltDecl tcEnv fvs) lcx impDs'
>     theta <- fetchSt
>     let impDs'' = map (uncurry (fixType . gen fvs lcx' . subst theta)) impDs'
>         tyEnv'' = rebindVars m tyEnv' (concatMap declVars impDs'')
>     (cx'',expDs') <-
>       mapAccumM (uncurry . tcCheckDecl m tcEnv tyEnv'') gcx expDs
>     return ((tyEnv'',cx''),impDs'' ++ expDs')
>   where (impDs,expDs) = partDecls sigs ds

> partDecls :: SigEnv -> [Decl a] -> ([Decl a],[(QualTypeExpr,Decl a)])
> partDecls sigs =
>   foldr (\d -> maybe (implicit d) (explicit d) (declTypeSig sigs d)) ([],[])
>   where implicit d ~(impDs,expDs) = (d:impDs,expDs)
>         explicit d ty ~(impDs,expDs) = (impDs,(ty,d):expDs)

> declTypeSig :: SigEnv -> Decl a -> Maybe QualTypeExpr
> declTypeSig sigs (FunctionDecl _ _ f _) = lookupEnv f sigs
> declTypeSig sigs (PatternDecl _ t _) =
>   case t of
>     VariablePattern _ v -> lookupEnv v sigs
>     _ -> Nothing

> bindVars :: ModuleIdent -> ValueEnv -> [(Ident,Int,TypeScheme)] -> ValueEnv
> bindVars m = foldr (uncurry3 (bindFun m))

> rebindVars :: ModuleIdent -> ValueEnv -> [(Ident,Int,TypeScheme)] -> ValueEnv
> rebindVars m = foldr (uncurry3 (rebindFun m))

> tcDeclVars :: TCEnv -> SigEnv -> Decl a -> TcState [(Ident,Int,TypeScheme)]
> tcDeclVars tcEnv sigs (FunctionDecl _ _ f eqs) =
>   case lookupEnv f sigs of
>     Just ty -> return [(f,n,typeScheme (expandPolyType tcEnv ty))]
>     Nothing ->
>       do
>         tys <- replicateM (n + 1) freshTypeVar
>         return [(f,n,monoType (foldr1 TypeArrow tys))]
>   where n = eqnArity (head eqs)
> tcDeclVars tcEnv sigs (PatternDecl p t _) =
>   case t of
>     VariablePattern _ v -> mapM (tcDeclVar True tcEnv sigs p) [v]
>     _ -> mapM (tcDeclVar False tcEnv sigs p) (bv t)

> tcDeclVar :: Bool -> TCEnv -> SigEnv -> Position -> Ident
>           -> TcState (Ident,Int,TypeScheme)
> tcDeclVar poly tcEnv sigs p v =
>   case lookupEnv v sigs of
>     Just ty
>       | poly || null (fv ty) ->
>           return (v,0,typeScheme (expandPolyType tcEnv ty))
>       | otherwise -> errorAt p (polymorphicVar v)
>     Nothing -> lambdaVar v

> tcDecl :: ModuleIdent -> TCEnv -> ValueEnv -> Context -> Decl a
>        -> TcState (Context,(Type,Decl QualType))
> tcDecl m tcEnv tyEnv cx (FunctionDecl p _ f eqs) =
>   tcFunctionDecl m tcEnv tyEnv cx (varType f tyEnv) p f eqs
> tcDecl m tcEnv tyEnv cx d@(PatternDecl p t rhs) =
>   do
>     (cx',ty',t') <- tcConstrTerm False tcEnv tyEnv p t
>     (cx'',rhs') <-
>       tcRhs m tcEnv tyEnv rhs >>-
>       unifyDecl p "pattern declaration" (ppDecl d) tcEnv tyEnv (cx++cx') ty'
>     return (cx'',(ty',PatternDecl p t' rhs'))

> tcFunctionDecl :: ModuleIdent -> TCEnv -> ValueEnv -> Context
>                -> TypeScheme -> Position -> Ident -> [Equation a]
>                -> TcState (Context,(Type,Decl QualType))
> tcFunctionDecl m tcEnv tyEnv cx (ForAll n ty) p f eqs =
>   do
>     theta <- fetchSt
>     (_,ty') <- inst (ForAll n ty)
>     (cx',eqs') <-
>       mapAccumM (tcEquation m tcEnv tyEnv (fsEnv (subst theta tyEnv)) ty' f)
>                 cx eqs
>     return (cx',(ty',FunctionDecl p ty f eqs'))

> tcEquation :: ModuleIdent -> TCEnv -> ValueEnv -> Set Int -> Type -> Ident
>            -> Context -> Equation a -> TcState (Context,Equation QualType)
> tcEquation m tcEnv tyEnv fs ty f cx eq@(Equation p lhs rhs) =
>   tcEqn m tcEnv tyEnv fs p lhs rhs >>-
>   unifyDecl p "equation" (ppEquation eq) tcEnv tyEnv cx ty

> tcEqn :: ModuleIdent -> TCEnv -> ValueEnv -> Set Int -> Position
>       -> Lhs a -> Rhs a -> TcState (Context,Type,Equation QualType)
> tcEqn m tcEnv tyEnv fs p lhs rhs =
>   do
>     tyEnv' <- bindLambdaVars m tyEnv lhs
>     (cx,tys,lhs') <- tcLhs tcEnv tyEnv' p lhs
>     (cx',ty,rhs') <- tcRhs m tcEnv tyEnv' rhs
>     cx'' <-
>       reduceContext p "equation" (ppEquation (Equation p lhs' rhs')) tcEnv
>                     (cx ++ cx')
>     checkSkolems p "Equation" ppEquation tcEnv tyEnv fs cx''
>                  (foldr TypeArrow ty tys) (Equation p lhs' rhs')

> bindLambdaVars :: QuantExpr t => ModuleIdent -> ValueEnv -> t
>                -> TcState ValueEnv
> bindLambdaVars m tyEnv t = liftM (bindVars m tyEnv) (mapM lambdaVar (bv t))

> lambdaVar :: Ident -> TcState (Ident,Int,TypeScheme)
> lambdaVar v = freshTypeVar >>= \ty -> return (v,0,monoType ty)

> tcGoal :: ModuleIdent -> TCEnv -> ValueEnv -> Goal a
>        -> TcState (Context,Type,Goal QualType)
> tcGoal m tcEnv tyEnv (Goal p e ds) =
>   do
>     (tyEnv',cx,ds') <- tcDecls m tcEnv tyEnv ds
>     (cx',ty,e') <- tcExpr m tcEnv tyEnv' p e
>     cx'' <- reduceContext p "goal" (ppExpr 0 e') tcEnv (cx ++ cx')
>     checkSkolems p "Goal" ppGoal tcEnv tyEnv zeroSet cx'' ty (Goal p e' ds')

> unifyDecl :: Position -> String -> Doc -> TCEnv -> ValueEnv -> Context -> Type
>           -> Context -> Type -> TcState Context
> unifyDecl p what doc tcEnv tyEnv cxLhs tyLhs cxRhs tyRhs =
>   do
>     cx <- unify p what doc tcEnv cxLhs tyLhs cxRhs tyRhs
>     theta <- fetchSt
>     let ty = subst theta tyLhs
>         fvs = foldr addToSet (fvEnv (subst theta tyEnv)) (typeVars ty)
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

> dfltDecl :: TCEnv -> Set Int -> Context -> Type -> Decl a -> TcState Context
> dfltDecl tcEnv fvs cx ty (FunctionDecl p _ f _) =
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
>     theta <- fetchSt
>     let ty' = subst theta ty
>         fvs' = foldr addToSet fvs (typeVars ty')
>     applyDefaults p what empty tcEnv fvs' cx ty'

\end{verbatim}
After \texttt{tcDeclGroup} has generalized the types of the implicitly
typed declarations of a declaration group it must update their left
hand side type annotations and the type environment accordingly.
Recall that the compiler generalizes only the types of variable and
function declarations.
\begin{verbatim}

> fixType :: TypeScheme -> Decl QualType -> Decl QualType
> fixType ~(ForAll _ ty) (FunctionDecl p _ f eqs) = FunctionDecl p ty f eqs
> fixType ty (PatternDecl p t rhs) = PatternDecl p (fixVarType ty t) rhs
>   where fixVarType ~(ForAll _ ty) t =
>           case t of
>             VariablePattern _ v -> VariablePattern ty v
>             _ -> t

> declVars :: Decl QualType -> [(Ident,Int,TypeScheme)]
> declVars (FunctionDecl _ ty f eqs) = [(f,eqnArity (head eqs),typeScheme ty)]
> declVars (PatternDecl _ t _) =
>   case t of
>     VariablePattern ty v -> [(v,0,typeScheme ty)]
>     _ -> []

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
>             -> Decl a -> TcState (Context,Decl QualType)
> tcCheckDecl m tcEnv tyEnv cx sigTy d =
>   do
>     (cx',(ty,d')) <- tcDecl m tcEnv tyEnv cx d
>     theta <- fetchSt
>     let fvs = fvEnv (subst theta tyEnv)
>         (gcx,lcx) = splitContext fvs cx'
>         ty' = subst theta ty
>         sigma = if poly then gen fvs lcx ty' else monoType ty'
>     checkDeclSig tcEnv sigTy gcx sigma d'
>   where poly = isNonExpansive tcEnv tyEnv d

> checkDeclSig :: TCEnv -> QualTypeExpr -> Context -> TypeScheme
>              -> Decl QualType -> TcState (Context,Decl QualType)
> checkDeclSig tcEnv sigTy cx sigma (FunctionDecl p _ f eqs)
>   | checkTypeSig tcEnv ty sigma = return (cx,FunctionDecl p ty f eqs)
>   | otherwise = errorAt p (typeSigTooGeneral tcEnv what sigTy sigma)
>   where what = text "Function:" <+> ppIdent f
>         ty = expandPolyType tcEnv sigTy
> checkDeclSig tcEnv sigTy cx sigma (PatternDecl p (VariablePattern _ v) rhs)
>   | checkTypeSig tcEnv ty sigma =
>       return (cx,PatternDecl p (VariablePattern ty v) rhs)
>   | otherwise = errorAt p (typeSigTooGeneral tcEnv what sigTy sigma)
>   where what = text "Variable:" <+> ppIdent v
>         ty = expandPolyType tcEnv sigTy

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
>   isNonExpansive _ _ (FunctionDecl _ _ _ _) = True
>   isNonExpansive _ _ (ForeignDecl _ _ _ _ _) = True
>   isNonExpansive tcEnv tyEnv (PatternDecl _ t rhs) =
>     isVariablePattern t && isNonExpansive tcEnv tyEnv rhs
>   isNonExpansive _ _ (FreeDecl _ _) = False
>   isNonExpansive _ _ (TrustAnnot _ _ _) = True

> instance Binding (Rhs a) where
>   isNonExpansive tcEnv tyEnv (SimpleRhs _ e ds) =
>     isNonExpansive tcEnv tyEnv' ds && isNonExpansive tcEnv tyEnv' e
>     where tyEnv' = foldr (bindDeclArity tcEnv) tyEnv ds
>   isNonExpansive _ _ (GuardedRhs _ _) = False

> instance Binding (Expression a) where
>   isNonExpansive tcEnv tyEnv = isNonExpansiveApp tcEnv tyEnv 0

> instance Binding a => Binding (Field a) where
>   isNonExpansive tcEnv tyEnv (Field _ e) = isNonExpansive tcEnv tyEnv e

> isNonExpansiveApp :: TCEnv -> ValueEnv -> Int -> Expression a -> Bool
> isNonExpansiveApp _ _ _ (Literal _ _) = True
> isNonExpansiveApp _ tyEnv n (Variable _ v)
>   | unqualify v == anonId = False
>   | isRenamed (unqualify v) = n == 0 || n < arity v tyEnv
>   | otherwise = n < arity v tyEnv
> isNonExpansiveApp _ _ _ (Constructor _ _) = True
> isNonExpansiveApp tcEnv tyEnv n (Paren e) = isNonExpansiveApp tcEnv tyEnv n e
> isNonExpansiveApp tcEnv tyEnv n (Typed e _) =
>   isNonExpansiveApp tcEnv tyEnv n e
> isNonExpansiveApp tcEnv tyEnv _ (Record _ _ fs) =
>   isNonExpansive tcEnv tyEnv fs
>   -- FIXME: stricly speaking a record construction is non-expansive
>   -- only if *all* field labels are present; for instance, (:){}
>   -- probably should be considered expansive
> isNonExpansiveApp tcEnv tyEnv _ (Tuple es) = isNonExpansive tcEnv tyEnv es
> isNonExpansiveApp tcEnv tyEnv _ (List _ es) = isNonExpansive tcEnv tyEnv es
> isNonExpansiveApp tcEnv tyEnv n (Apply f e) =
>   isNonExpansiveApp tcEnv tyEnv (n + 1) f && isNonExpansive tcEnv tyEnv e
> isNonExpansiveApp tcEnv tyEnv n (InfixApply e1 op e2) =
>   isNonExpansiveApp tcEnv tyEnv (n + 2) (infixOp op) &&
>   isNonExpansive tcEnv tyEnv e1 && isNonExpansive tcEnv tyEnv e2
> isNonExpansiveApp tcEnv tyEnv n (LeftSection e op) =
>   isNonExpansiveApp tcEnv tyEnv (n + 1) (infixOp op) &&
>   isNonExpansive tcEnv tyEnv e
> isNonExpansiveApp tcEnv tyEnv n (Lambda _ ts e) =
>   n < length ts ||
>   all isVarPattern ts && isNonExpansiveApp tcEnv tyEnv' (n - length ts) e
>   where tyEnv' = foldr bindVarArity tyEnv (bv ts)
> isNonExpansiveApp tcEnv tyEnv n (Let ds e) =
>   isNonExpansive tcEnv tyEnv' ds && isNonExpansiveApp tcEnv tyEnv' n e
>   where tyEnv' = foldr (bindDeclArity tcEnv) tyEnv ds
> isNonExpansiveApp _ _ _ _ = False

> bindDeclArity :: TCEnv -> Decl a -> ValueEnv -> ValueEnv
> bindDeclArity _ (InfixDecl _ _ _ _) tyEnv = tyEnv
> bindDeclArity _ (TypeSig _ _ _) tyEnv = tyEnv
> bindDeclArity _ (FunctionDecl _ _ f eqs) tyEnv =
>   bindArity f (eqnArity (head eqs)) tyEnv
> bindDeclArity tcEnv (ForeignDecl _ _ _ f ty) tyEnv =
>   bindArity f (foreignArity ty') tyEnv
>   where ty' = unqualType (expandPolyType tcEnv (QualTypeExpr [] ty))
> bindDeclArity _ (PatternDecl _ t _) tyEnv = foldr bindVarArity tyEnv (bv t)
> bindDeclArity _ (FreeDecl _ vs) tyEnv = foldr bindVarArity tyEnv (bv vs)
> bindDeclArity _ (TrustAnnot _ _ _) tyEnv = tyEnv

> bindVarArity :: Ident -> ValueEnv -> ValueEnv
> bindVarArity v tyEnv = bindArity v 0 tyEnv

> bindArity :: Ident -> Int -> ValueEnv -> ValueEnv
> bindArity v n tyEnv = localBindTopEnv v (Value (qualify v) n undefined) tyEnv

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

> tcTopDecl :: ModuleIdent -> TCEnv -> ValueEnv -> TopDecl a
>           -> TcState (TopDecl QualType)
> tcTopDecl _ _ _ (DataDecl p cx tc tvs cs clss) =
>   return (DataDecl p cx tc tvs cs clss)
> tcTopDecl _ _ _ (NewtypeDecl p cx tc tvs nc clss) =
>   return (NewtypeDecl p cx tc tvs nc clss)
> tcTopDecl _ _ _ (TypeDecl p tc tvs ty) = return (TypeDecl p tc tvs ty)
> tcTopDecl m tcEnv tyEnv (ClassDecl p cx cls tv ds) =
>   do
>     vds' <- mapM (tcClassMethodDecl m tcEnv tyEnv (qualify cls) tv sigs) vds
>     return (ClassDecl p cx cls tv (map untyped ods ++ vds'))
>   where sigs = foldr bindTypeSigs noSigs ods
>         (vds,ods) = partition isValueDecl ds
> tcTopDecl m tcEnv tyEnv (InstanceDecl p cx cls ty ds) =
>   do
>     vds' <- mapM (tcInstMethodDecl m tcEnv tyEnv cls' ty') vds
>     return (InstanceDecl p cx cls ty (map untyped ods ++ vds'))
>   where cls' = origName (head (qualLookupTopEnv cls tcEnv))
>         ty' = expandPolyType tcEnv (QualTypeExpr cx ty)
>         (vds,ods) = partition isValueDecl ds
> tcTopDecl _ _ _ (DefaultDecl p tys) = return (DefaultDecl p tys)
> tcTopDecl _ _ _ (BlockDecl _) = internalError "tcTopDecl"

> tcClassMethodDecl :: ModuleIdent -> TCEnv -> ValueEnv -> QualIdent -> Ident
>                   -> SigEnv -> Decl a -> TcState (Decl QualType)
> tcClassMethodDecl m tcEnv tyEnv cls tv sigs d =
>   do
>     (ty',d') <- tcMethodDecl m tcEnv tyEnv methTy d
>     checkClassMethodType tcEnv (clsType cls tv (classMethodSig sigs d)) ty' d'
>   where methTy = classMethodType (qualifyWith m) d tyEnv
>         clsType cls tv (QualTypeExpr cx ty) =
>           QualTypeExpr (ClassAssert cls (VariableType tv) : cx) ty

> checkClassMethodType :: TCEnv -> QualTypeExpr -> TypeScheme -> Decl QualType
>                      -> TcState (Decl QualType)
> checkClassMethodType tcEnv sigTy sigma (FunctionDecl p ty f eqs)
>   | checkTypeSig tcEnv (expandPolyType tcEnv sigTy) sigma =
>       return (FunctionDecl p ty f eqs)
>   | otherwise = errorAt p (typeSigTooGeneral tcEnv what sigTy sigma)
>   where what = text "Method:" <+> ppIdent f

> tcInstMethodDecl :: ModuleIdent -> TCEnv -> ValueEnv -> QualIdent -> QualType
>                  -> Decl a -> TcState (Decl QualType)
> tcInstMethodDecl m tcEnv tyEnv cls instTy d =
>   do
>     (ty',d') <- tcMethodDecl m tcEnv tyEnv (typeScheme methTy) d
>     checkInstMethodType tcEnv (normalize 0 methTy) ty' d'
>   where methTy = instMethodType (qualifyLike cls) instTy d tyEnv

> checkInstMethodType :: TCEnv -> QualType -> TypeScheme -> Decl QualType
>                     -> TcState (Decl QualType)
> checkInstMethodType tcEnv methTy sigma (FunctionDecl p ty f eqs)
>   | checkTypeSig tcEnv methTy sigma = return (FunctionDecl p ty f eqs)
>   | otherwise = errorAt p (methodSigTooGeneral tcEnv what methTy sigma)
>   where what = text "Method:" <+> ppIdent f

> tcMethodDecl :: ModuleIdent -> TCEnv -> ValueEnv -> TypeScheme -> Decl a
>              -> TcState (TypeScheme,Decl QualType)
> tcMethodDecl m tcEnv tyEnv methTy (FunctionDecl p _ f eqs) =
>   do
>     (cx,(ty,d')) <- tcFunctionDecl m tcEnv tyEnv' [] methTy p f eqs
>     theta <- fetchSt
>     return (gen zeroSet cx (subst theta ty),d')
>   where tyEnv' = bindFun m f (eqnArity (head eqs)) methTy tyEnv

> classMethodSig :: SigEnv -> Decl a -> QualTypeExpr
> classMethodSig sigs (FunctionDecl _ _ f _) =
>   fromJust (lookupEnv (unRenameIdent f) sigs)

> classMethodType :: (Ident -> QualIdent) -> Decl a -> ValueEnv -> TypeScheme
> classMethodType qualify (FunctionDecl _ _ f _) tyEnv =
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

> tcForeignFunct :: ModuleIdent -> TCEnv -> ValueEnv
>                -> Position -> ForeignImport -> Ident -> TypeExpr
>                -> TcState (ValueEnv,Type)
> tcForeignFunct m tcEnv tyEnv p (cc,_,ie) f ty =
>   do
>     checkForeignType cc ty'
>     return (bindFun m f (foreignArity ty') (polyType ty') tyEnv,ty')
>   where ty' = unqualType (expandPolyType tcEnv (QualTypeExpr [] ty))
>         checkForeignType cc ty
>           | cc == CallConvPrimitive = return ()
>           | ie == Just "dynamic" = checkCDynCallType tcEnv p cc ty
>           | maybe False ('&' `elem`) ie = checkCAddrType tcEnv p ty
>           | otherwise = checkCCallType tcEnv p cc ty

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
constructor itself. Overloaded (numeric) literals are supported in
expressions and patterns of case alternatives, but not in other
patterns.

\ToDo{The types admissible for numeric literals in patterns without
  overloading should in some way acknowledge the set of types
  specified in a default declaration if one is present.}

When computing the type of a variable in a pattern, we ignore the
context of the variable's type (which can only be due to a type
signature in the same declaration group) for just the same reason as
in \texttt{tcFunctionDecl} above.
\begin{verbatim}

> tcLiteral :: Bool -> Literal -> TcState (Context,Type)
> tcLiteral _ (Char _) = return ([],charType)
> tcLiteral poly (Integer _)
>   | poly = freshNumType
>   | otherwise = liftM ((,) []) (freshConstrained numTypes)
> tcLiteral poly (Rational _)
>   | poly = freshFracType
>   | otherwise = liftM ((,) []) (freshConstrained fracTypes)
> tcLiteral _ (String _) = return ([],stringType)

> tcLhs :: TCEnv -> ValueEnv -> Position -> Lhs a
>       -> TcState (Context,[Type],Lhs QualType)
> tcLhs tcEnv tyEnv p (FunLhs f ts) =
>   do
>     (cxs,tys,ts') <- liftM unzip3 $ mapM (tcConstrTerm False tcEnv tyEnv p) ts
>     return (concat cxs,tys,FunLhs f ts')
> tcLhs tcEnv tyEnv p (OpLhs t1 op t2) =
>   do
>     (cx1,ty1,t1') <- tcConstrTerm False tcEnv tyEnv p t1
>     (cx2,ty2,t2') <- tcConstrTerm False tcEnv tyEnv p t2
>     return (cx1 ++ cx2,[ty1,ty2],OpLhs t1' op t2')
> tcLhs tcEnv tyEnv p (ApLhs lhs ts) =
>   do
>     (cx,tys1,lhs') <- tcLhs tcEnv tyEnv p lhs
>     (cxs,tys2,ts') <-
>       liftM unzip3 $ mapM (tcConstrTerm False tcEnv tyEnv p) ts
>     return (cx ++ concat cxs,tys1 ++ tys2,ApLhs lhs' ts')

> tcConstrTerm :: Bool -> TCEnv -> ValueEnv -> Position -> ConstrTerm a
>              -> TcState (Context,Type,ConstrTerm QualType)
> tcConstrTerm poly _ _ _ (LiteralPattern _ l) =
>   do
>     (cx,ty) <- tcLiteral poly l
>     return (cx,ty,LiteralPattern (qualType ty) l)
> tcConstrTerm poly _ _ _ (NegativePattern _ l) =
>   do
>     (cx,ty) <- tcLiteral poly l
>     return (cx,ty,NegativePattern (qualType ty) l)
> tcConstrTerm _ _ tyEnv _ (VariablePattern _ v) =
>   do
>     (_,ty) <- inst (varType v tyEnv)
>     return ([],ty,VariablePattern (qualType ty) v)
> tcConstrTerm poly tcEnv tyEnv p t@(ConstructorPattern _ c ts) =
>   do
>     (cx,ty) <- skol tcEnv (conType c tyEnv)
>     tcConstrApp poly tcEnv tyEnv p (ppConstrTerm 0 t) c cx ty ts
> tcConstrTerm poly tcEnv tyEnv p t@(FunctionPattern _ f ts) =
>   do
>     (cx,ty) <- inst (funType f tyEnv)
>     tcFunctPattern poly tcEnv tyEnv p (ppConstrTerm 0 t) f id cx ty ts
> tcConstrTerm poly tcEnv tyEnv p t@(InfixPattern _ t1 op t2) =
>   do
>     (cx,ty) <- tcPatternOp tcEnv tyEnv p op
>     (alpha,beta,gamma) <-
>       tcBinary p "infix pattern" (doc $-$ text "Operator:" <+> ppOp op)
>                tcEnv ty
>     (cx',t1') <- tcConstrArg poly tcEnv tyEnv p "pattern" doc cx alpha t1
>     (cx'',t2') <- tcConstrArg poly tcEnv tyEnv p "pattern" doc cx' beta t2
>     return (cx'',gamma,InfixPattern (qualType gamma) t1' op t2')
>   where doc = ppConstrTerm 0 t
> tcConstrTerm poly tcEnv tyEnv p (ParenPattern t) =
>   do
>     (cx,ty,t') <- tcConstrTerm poly tcEnv tyEnv p t
>     return (cx,ty,ParenPattern t')
> tcConstrTerm poly tcEnv tyEnv p t@(RecordPattern _ c fs) =
>   do
>     (cx,ty) <- liftM (apSnd arrowBase) (skol tcEnv (conType c tyEnv))
>     (cx',fs') <-
>       mapAccumM (tcField (tcConstrTerm poly) "pattern" doc tcEnv tyEnv p ty)
>                 cx fs
>     return (cx',ty,RecordPattern (qualType ty) c fs')
>   where doc t1 = ppConstrTerm 0 t $-$ text "Term:" <+> ppConstrTerm 0 t1
> tcConstrTerm poly tcEnv tyEnv p (TuplePattern ts) =
>   do
>     (cxs,tys,ts') <- liftM unzip3 $ mapM (tcConstrTerm poly tcEnv tyEnv p) ts
>     return (concat cxs,tupleType tys,TuplePattern ts')
> tcConstrTerm poly tcEnv tyEnv p t@(ListPattern _ ts) =
>   do
>     ty <- freshTypeVar
>     (cx,ts') <-
>       mapAccumM (flip (tcConstrArg poly tcEnv tyEnv p "pattern" doc) ty) [] ts
>     return (cx,listType ty,ListPattern (qualType (listType ty)) ts')
>   where doc = ppConstrTerm 0 t
> tcConstrTerm poly tcEnv tyEnv p t@(AsPattern v t') =
>   do
>     (_,ty) <- inst (varType v tyEnv)
>     (cx,t'') <-
>       tcConstrTerm poly tcEnv tyEnv p t' >>-
>       unify p "pattern" (ppConstrTerm 0 t) tcEnv [] ty
>     return (cx,ty,AsPattern v t'')
> tcConstrTerm _ tcEnv tyEnv p (LazyPattern t) =
>   do
>     (cx,ty,t') <- tcConstrTerm False tcEnv tyEnv p t
>     return (cx,ty,LazyPattern t')

> tcConstrApp :: Bool -> TCEnv -> ValueEnv -> Position -> Doc -> QualIdent
>             -> Context -> Type -> [ConstrTerm a]
>             -> TcState (Context,Type,ConstrTerm QualType)
> tcConstrApp poly tcEnv tyEnv p doc c cx ty ts =
>   do
>     unless (length tys == n) (errorAt p (wrongArity c (length tys) n))
>     (cx',ts') <-
>       mapAccumM (uncurry . tcConstrArg poly tcEnv tyEnv p "pattern" doc) cx
>                 (zip tys ts)
>     return (cx',ty',ConstructorPattern (qualType ty') c ts')
>   where (tys,ty') = arrowUnapply ty
>         n = length ts

> tcFunctPattern :: Bool -> TCEnv -> ValueEnv -> Position -> Doc -> QualIdent
>                -> ([ConstrTerm QualType] -> [ConstrTerm QualType])
>                -> Context -> Type -> [ConstrTerm a]
>                -> TcState (Context,Type,ConstrTerm QualType)
> tcFunctPattern _ _ _ _ _ f ts cx ty [] =
>   return (cx,ty,FunctionPattern (qualType ty) f (ts []))
> tcFunctPattern poly tcEnv tyEnv p doc f ts cx ty (t':ts') =
>   do
>     (alpha,beta) <-
>       tcArrow p "pattern" (doc $-$ text "Term:" <+> ppConstrTerm 0 t) tcEnv ty
>     (cx',t'') <- tcConstrArg poly tcEnv tyEnv p "pattern" doc cx alpha t'
>     tcFunctPattern poly tcEnv tyEnv p doc f (ts . (t'':)) cx' beta ts'
>   where t = FunctionPattern (qualType ty) f (ts [])

> tcConstrArg :: Bool -> TCEnv -> ValueEnv -> Position -> String -> Doc
>             -> Context -> Type -> ConstrTerm a
>             -> TcState (Context,ConstrTerm QualType)
> tcConstrArg poly tcEnv tyEnv p what doc cx ty t =
>   tcConstrTerm poly tcEnv tyEnv p t >>-
>   unify p what (doc $-$ text "Term:" <+> ppConstrTerm 0 t) tcEnv cx ty

> tcPatternOp :: TCEnv -> ValueEnv -> Position -> InfixOp a
>             -> TcState (Context,Type)
> tcPatternOp tcEnv tyEnv p (InfixConstr _ op) =
>   do
>     (cx,ty) <- skol tcEnv (conType op tyEnv)
>     unless (arrowArity ty == 2) (errorAt p (wrongArity op (arrowArity ty) 2))
>     return (cx,ty)
> tcPatternOp _ tyEnv _ (InfixOp _ op) = inst (funType op tyEnv)

> tcRhs :: ModuleIdent -> TCEnv -> ValueEnv -> Rhs a
>       -> TcState (Context,Type,Rhs QualType)
> tcRhs m tcEnv tyEnv (SimpleRhs p e ds) =
>   do
>     (tyEnv',cx,ds') <- tcDecls m tcEnv tyEnv ds
>     (cx',ty,e') <- tcExpr m tcEnv tyEnv' p e
>     cx'' <- reduceContext p "expression" (ppExpr 0 e') tcEnv (cx ++ cx')
>     return (cx'',ty,SimpleRhs p e' ds')
> tcRhs m tcEnv tyEnv (GuardedRhs es ds) =
>   do
>     (tyEnv',cx,ds') <- tcDecls m tcEnv tyEnv ds
>     gty <- guardType es
>     ty <- freshTypeVar
>     (cx',es') <- mapAccumM (tcCondExpr m tcEnv tyEnv' gty ty) cx es
>     return (cx',ty,GuardedRhs es' ds')
>   where guardType es
>           | length es > 1 = return boolType
>           | otherwise = freshConstrained guardTypes

> tcCondExpr :: ModuleIdent -> TCEnv -> ValueEnv -> Type -> Type -> Context
>            -> CondExpr a -> TcState (Context,CondExpr QualType)
> tcCondExpr m tcEnv tyEnv gty ty cx (CondExpr p g e) =
>   do
>     (cx',g') <-
>       tcExpr m tcEnv tyEnv p g >>- unify p "guard" (ppExpr 0 g) tcEnv cx gty
>     (cx'',e') <-
>       tcExpr m tcEnv tyEnv p e >>-
>       unify p "expression" (ppExpr 0 e) tcEnv cx' ty
>     return (cx'',CondExpr p g' e')

> tcExpr :: ModuleIdent -> TCEnv -> ValueEnv -> Position -> Expression a
>        -> TcState (Context,Type,Expression QualType)
> tcExpr _ _ _ _ (Literal _ l) =
>   do
>     (cx,ty) <- tcLiteral True l
>     return (cx,ty,Literal (qualType ty) l)
> tcExpr _ _ tyEnv _ (Variable _ v) =
>   do
>     (cx,ty) <-
>       if unRenameIdent (unqualify v) == anonId then freshQualType []
>       else inst (funType v tyEnv)
>     return (cx,ty,Variable (qualType ty) v)
> tcExpr _ _ tyEnv _ (Constructor _ c) =
>   do
>     (cx,ty) <- inst (thd3 (conType c tyEnv))
>     return (cx,ty,Constructor (qualType ty) c)
> tcExpr m tcEnv tyEnv p (Typed e sig) =
>   do
>     (cx,ty) <- inst (typeScheme sigTy)
>     (cx',e') <-
>       tcExpr m tcEnv tyEnv p e >>-
>       unifyDecl p "explicitly typed expression" (ppExpr 0 e) tcEnv tyEnv [] ty
>     theta <- fetchSt
>     let fvs = fvEnv (subst theta tyEnv)
>         (gcx,lcx) = splitContext fvs cx'
>         sigma = gen fvs lcx (subst theta ty)
>     unless (checkTypeSig tcEnv sigTy sigma)
>       (errorAt p (typeSigTooGeneral tcEnv (text "Expression:" <+> ppExpr 0 e)
>                                     sig sigma))
>     return (cx ++ gcx,ty,Typed e' sig)
>   where sigTy = expandPolyType tcEnv sig
> tcExpr m tcEnv tyEnv p (Paren e) =
>   do
>     (cx,ty,e') <- tcExpr m tcEnv tyEnv p e
>     return (cx,ty,Paren e')
> tcExpr m tcEnv tyEnv p e@(Record _ c fs) =
>   do
>     (cx,ty) <- liftM (apSnd arrowBase) (inst (thd3 (conType c tyEnv)))
>     (cx',fs') <-
>       mapAccumM (tcField (tcExpr m) "construction" doc tcEnv tyEnv p ty) cx fs
>     return (cx',ty,Record (qualType ty) c fs')
>   where doc e1 = ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1
> tcExpr m tcEnv tyEnv p e@(RecordUpdate e1 fs) =
>   do
>     (cx,ty,e1') <- tcExpr m tcEnv tyEnv p e1
>     (cx',fs') <-
>       mapAccumM (tcField (tcExpr m) "update" doc tcEnv tyEnv p ty) cx fs
>     return (cx',ty,RecordUpdate e1' fs')
>   where doc e1 = ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1
> tcExpr m tcEnv tyEnv p (Tuple es) =
>   do
>     (cxs,tys,es') <- liftM unzip3 $ mapM (tcExpr m tcEnv tyEnv p) es
>     return (concat cxs,tupleType tys,Tuple es')
> tcExpr m tcEnv tyEnv p e@(List _ es) =
>   do
>     ty <- freshTypeVar
>     (cx,es') <-
>       mapAccumM (flip (tcArg m tcEnv tyEnv p "expression" doc) ty) [] es
>     return (cx,listType ty,List (qualType (listType ty)) es')
>   where doc = ppExpr 0 e
> tcExpr m tcEnv tyEnv p (ListCompr e qs) =
>   do
>     fs <- liftM (fsEnv . flip subst tyEnv) fetchSt
>     ((tyEnv',cx),qs') <-
>       mapAccumM (uncurry (flip (tcQual m tcEnv) p)) (tyEnv,[]) qs
>     (cx',ty,e') <- tcExpr m tcEnv tyEnv' p e
>     cx'' <- reduceContext p "expression" (ppExpr 0 e') tcEnv (cx ++ cx')
>     checkSkolems p "Expression" (ppExpr 0) tcEnv tyEnv fs cx'' (listType ty)
>                  (ListCompr e' qs')
> tcExpr m tcEnv tyEnv p e@(EnumFrom e1) =
>   do
>     (cx,ty) <- freshEnumType
>     (cx',e1') <-
>       tcArg m tcEnv tyEnv p "arithmetic sequence" (ppExpr 0 e) cx ty e1
>     return (cx',listType ty,EnumFrom e1')
> tcExpr m tcEnv tyEnv p e@(EnumFromThen e1 e2) =
>   do
>     (cx,ty) <- freshEnumType
>     (cx',e1') <-
>       tcArg m tcEnv tyEnv p "arithmetic sequence" (ppExpr 0 e) cx ty e1
>     (cx'',e2') <-
>       tcArg m tcEnv tyEnv p "arithmetic sequence" (ppExpr 0 e) cx' ty e2
>     return (cx'',listType ty,EnumFromThen e1' e2')
> tcExpr m tcEnv tyEnv p e@(EnumFromTo e1 e2) =
>   do
>     (cx,ty) <- freshEnumType
>     (cx',e1') <-
>       tcArg m tcEnv tyEnv p "arithmetic sequence" (ppExpr 0 e) cx ty e1
>     (cx'',e2') <-
>       tcArg m tcEnv tyEnv p "arithmetic sequence" (ppExpr 0 e) cx' ty e2
>     return (cx'',listType ty,EnumFromTo e1' e2')
> tcExpr m tcEnv tyEnv p e@(EnumFromThenTo e1 e2 e3) =
>   do
>     (cx,ty) <- freshEnumType
>     (cx',e1') <-
>       tcArg m tcEnv tyEnv p "arithmetic sequence" (ppExpr 0 e) cx ty e1
>     (cx'',e2') <-
>       tcArg m tcEnv tyEnv p "arithmetic sequence" (ppExpr 0 e) cx' ty e2
>     (cx''',e3') <-
>       tcArg m tcEnv tyEnv p "arithmetic sequence" (ppExpr 0 e) cx'' ty e3
>     return (cx''',listType ty,EnumFromThenTo e1' e2' e3')
> tcExpr m tcEnv tyEnv p e@(UnaryMinus e1) =
>   do
>     (cx,ty) <- freshNumType
>     (cx',e1') <- tcArg m tcEnv tyEnv p "unary negation" (ppExpr 0 e) cx ty e1
>     return (cx',ty,UnaryMinus e1')
> tcExpr m tcEnv tyEnv p e@(Apply e1 e2) =
>   do
>     (cx,(alpha,beta),e1') <-
>       tcExpr m tcEnv tyEnv p e1 >>=-
>       tcArrow p "application" (ppExpr 0 e $-$ text "Term:" <+> ppExpr 0 e1)
>               tcEnv
>     (cx',e2') <- tcArg m tcEnv tyEnv p "application" (ppExpr 0 e) cx alpha e2
>     return (cx',beta,Apply e1' e2')
> tcExpr m tcEnv tyEnv p e@(InfixApply e1 op e2) =
>   do
>     (cx,(alpha,beta,gamma),op') <-
>       tcInfixOp tyEnv op >>=-
>       tcBinary p "infix application"
>                (ppExpr 0 e $-$ text "Operator:" <+> ppOp op) tcEnv
>     (cx',e1') <-
>       tcArg m tcEnv tyEnv p "infix application" (ppExpr 0 e) cx alpha e1
>     (cx'',e2') <-
>       tcArg m tcEnv tyEnv p "infix application" (ppExpr 0 e) cx' beta e2
>     return (cx'',gamma,InfixApply e1' op' e2')
> tcExpr m tcEnv tyEnv p e@(LeftSection e1 op) =
>   do
>     (cx,(alpha,beta),op') <-
>       tcInfixOp tyEnv op >>=-
>       tcArrow p "left section" (ppExpr 0 e $-$ text "Operator:" <+> ppOp op)
>               tcEnv
>     (cx',e1') <- tcArg m tcEnv tyEnv p "left section" (ppExpr 0 e) cx alpha e1
>     return (cx',beta,LeftSection e1' op')
> tcExpr m tcEnv tyEnv p e@(RightSection op e1) =
>   do
>     (cx,(alpha,beta,gamma),op') <-
>       tcInfixOp tyEnv op >>=-
>       tcBinary p "right section"
>                (ppExpr 0 e $-$ text "Operator:" <+> ppOp op) tcEnv
>     (cx',e1') <- tcArg m tcEnv tyEnv p "right section" (ppExpr 0 e) cx beta e1
>     return (cx',TypeArrow alpha gamma,RightSection op' e1')
> tcExpr m tcEnv tyEnv _ (Lambda p ts e) =
>   do
>     fs <- liftM (fsEnv . flip subst tyEnv) fetchSt
>     tyEnv' <- bindLambdaVars m tyEnv ts
>     (cxs,tys,ts') <-
>       liftM unzip3 $ mapM (tcConstrTerm False tcEnv tyEnv' p) ts
>     (cx,ty,e') <- tcExpr m tcEnv tyEnv' p e
>     cx' <- reduceContext p "expression" (ppExpr 0 e') tcEnv (concat cxs ++ cx)
>     checkSkolems p "Expression" (ppExpr 0) tcEnv tyEnv fs cx'
>                  (foldr TypeArrow ty tys) (Lambda p ts' e')
> tcExpr m tcEnv tyEnv p (Let ds e) =
>   do
>     fs <- liftM (fsEnv . flip subst tyEnv) fetchSt
>     (tyEnv',cx,ds') <- tcDecls m tcEnv tyEnv ds
>     (cx',ty,e') <- tcExpr m tcEnv tyEnv' p e
>     cx'' <- reduceContext p "expression" (ppExpr 0 e') tcEnv (cx ++ cx')
>     checkSkolems p "Expression" (ppExpr 0) tcEnv tyEnv fs cx'' ty (Let ds' e')
> tcExpr m tcEnv tyEnv p (Do sts e) =
>   do
>     fs <- liftM (fsEnv . flip subst tyEnv) fetchSt
>     ((tyEnv',cx,mTy),sts') <-
>       mapAccumM (uncurry3 (flip (tcStmt m tcEnv) p)) (tyEnv,[],Nothing) sts
>     ty <- liftM (maybe id TypeApply mTy) freshTypeVar
>     (cx',e') <-
>       tcExpr m tcEnv tyEnv' p e >>-
>       unify p "statement" (ppExpr 0 e) tcEnv cx ty
>     checkSkolems p "Expression" (ppExpr 0) tcEnv tyEnv fs cx' ty (Do sts' e')
> tcExpr m tcEnv tyEnv p e@(IfThenElse e1 e2 e3) =
>   do
>     (cx,e1') <- tcArg m tcEnv tyEnv p "expression" (ppExpr 0 e) [] boolType e1
>     (cx',ty,e2') <- tcExpr m tcEnv tyEnv p e2
>     (cx'',e3') <-
>       tcArg m tcEnv tyEnv p "expression" (ppExpr 0 e) (cx ++ cx') ty e3
>     return (cx'',ty,IfThenElse e1' e2' e3')
> tcExpr m tcEnv tyEnv p (Case e as) =
>   do
>     (cx,tyLhs,e') <- tcExpr m tcEnv tyEnv p e
>     tyRhs <- freshTypeVar
>     fs <- liftM (fsEnv . flip subst tyEnv) fetchSt
>     (cx',as') <- mapAccumM (tcAlt True m tcEnv tyEnv fs tyLhs tyRhs) cx as
>     return (cx',tyRhs,Case e' as')
> tcExpr m tcEnv tyEnv p (Fcase e as) =
>   do
>     (cx,tyLhs,e') <- tcExpr m tcEnv tyEnv p e
>     tyRhs <- freshTypeVar
>     fs <- liftM (fsEnv . flip subst tyEnv) fetchSt
>     (cx',as') <- mapAccumM (tcAlt False m tcEnv tyEnv fs tyLhs tyRhs) cx as
>     return (cx',tyRhs,Fcase e' as')

> tcArg :: ModuleIdent -> TCEnv -> ValueEnv -> Position -> String -> Doc
>       -> Context -> Type -> Expression a
>       -> TcState (Context,Expression QualType)
> tcArg m tcEnv tyEnv p what doc cx ty e =
>   tcExpr m tcEnv tyEnv p e >>-
>   unify p what (doc $-$ text "Term:" <+> ppExpr 0 e) tcEnv cx ty

> tcAlt :: Bool -> ModuleIdent -> TCEnv -> ValueEnv -> Set Int -> Type -> Type
>       -> Context -> Alt a -> TcState (Context,Alt QualType)
> tcAlt poly m tcEnv tyEnv fs tyLhs tyRhs cx a@(Alt p t rhs) =
>   tcAltern poly m tcEnv tyEnv fs tyLhs tyRhs p t rhs >>- 
>   unify p "case alternative" (ppAlt a) tcEnv cx tyRhs

> tcAltern :: Bool -> ModuleIdent -> TCEnv -> ValueEnv -> Set Int
>          -> Type -> Type -> Position -> ConstrTerm a -> Rhs a
>          -> TcState (Context,Type,Alt QualType)
> tcAltern poly m tcEnv tyEnv fs tyLhs tyRhs p t rhs =
>   do
>     tyEnv' <- bindLambdaVars m tyEnv t
>     (cx,t') <- tcConstrArg poly tcEnv tyEnv' p "case pattern" doc [] tyLhs t
>     (cx',ty',rhs') <- tcRhs m tcEnv tyEnv' rhs
>     cx'' <-
>       reduceContext p "alternative" (ppAlt (Alt p t' rhs')) tcEnv (cx ++ cx')
>     checkSkolems p "Alternative" ppAlt tcEnv tyEnv fs cx'' ty' (Alt p t' rhs')
>   where doc = ppAlt (Alt p t rhs)

> tcQual :: ModuleIdent -> TCEnv -> ValueEnv -> Position -> Context
>        -> Statement a -> TcState ((ValueEnv,Context),Statement QualType)
> tcQual m tcEnv tyEnv p cx (StmtExpr e) =
>   do
>     (cx',e') <-
>       tcExpr m tcEnv tyEnv p e >>-
>       unify p "guard" (ppExpr 0 e) tcEnv cx boolType
>     return ((tyEnv,cx'),StmtExpr e')
> tcQual m tcEnv tyEnv _ cx q@(StmtBind p t e) =
>   do
>     alpha <- freshTypeVar
>     (cx',e') <-
>       tcArg m tcEnv tyEnv p "generator" (ppStmt q) cx (listType alpha) e
>     tyEnv' <- bindLambdaVars m tyEnv t
>     (cx'',t') <-
>       tcConstrArg False tcEnv tyEnv' p "generator" (ppStmt q) cx' alpha t
>     return ((tyEnv',cx''),StmtBind p t' e')
> tcQual m tcEnv tyEnv _ cx (StmtDecl ds) =
>   do
>     (tyEnv',cx',ds') <- tcDecls m tcEnv tyEnv ds
>     return ((tyEnv',cx ++ cx'),StmtDecl ds')

> tcStmt :: ModuleIdent -> TCEnv -> ValueEnv -> Position
>        -> Context -> Maybe Type -> Statement a
>        -> TcState ((ValueEnv,Context,Maybe Type),Statement QualType)
> tcStmt m tcEnv tyEnv p cx mTy (StmtExpr e) =
>   do
>     (cx',ty) <- maybe freshMonadType (return . (,) []) mTy
>     alpha <- freshTypeVar
>     (cx'',e') <-
>       tcExpr m tcEnv tyEnv p e >>-
>       unify p "statement" (ppExpr 0 e) tcEnv (cx ++ cx') (TypeApply ty alpha)
>     return ((tyEnv,cx'',Just ty),StmtExpr e')
> tcStmt m tcEnv tyEnv _ cx mTy st@(StmtBind p t e) =
>   do
>     (cx',ty) <- maybe freshMonadType (return . (,) []) mTy
>     alpha <- freshTypeVar
>     (cx'',e') <-
>       tcArg m tcEnv tyEnv p "statement" (ppStmt st) (cx ++ cx')
>             (TypeApply ty alpha) e
>     tyEnv' <- bindLambdaVars m tyEnv t
>     (cx''',t') <-
>       tcConstrArg False tcEnv tyEnv' p "statement" (ppStmt st) cx'' alpha t
>     return ((tyEnv',cx''',Just ty),StmtBind p t' e')
> tcStmt m tcEnv tyEnv _ cx mTy (StmtDecl ds) =
>   do
>     (tyEnv',cx',ds') <- tcDecls m tcEnv tyEnv ds
>     return ((tyEnv',cx ++ cx',mTy),StmtDecl ds')

> tcInfixOp :: ValueEnv -> InfixOp a -> TcState (Context,Type,InfixOp QualType)
> tcInfixOp tyEnv (InfixOp _ op) =
>   do
>     (cx,ty) <- inst (funType op tyEnv)
>     return (cx,ty,InfixOp (qualType ty) op)
> tcInfixOp tyEnv (InfixConstr a op) =
>   do
>     (cx,ty) <- inst (thd3 (conType op tyEnv))
>     return (cx,ty,InfixConstr (qualType ty) op)

> tcField :: (TCEnv -> ValueEnv -> Position -> a b
>             -> TcState (Context,Type,a QualType))
>         -> String -> (a b -> Doc) -> TCEnv -> ValueEnv -> Position -> Type
>         -> Context -> Field (a b) -> TcState (Context,Field (a QualType))
> tcField tc what doc tcEnv tyEnv p ty cx (Field l x) =
>   do
>     (cx',TypeArrow ty1 ty2) <- inst (funType l tyEnv)
>     -- NB the following unification cannot fail; it serves only for
>     --    instantiating the type variables in the field label's type
>     unify p "field label" empty tcEnv [] ty [] ty1
>     (cx'',x') <-
>       tc tcEnv tyEnv p x >>-
>       unify p ("record " ++ what) (doc x) tcEnv (cx ++ cx') ty2
>     return (cx'',Field l x')

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
>     theta <- fetchSt
>     unaryArrow (subst theta ty)
>   where unaryArrow (TypeArrow ty1 ty2) = return (ty1,ty2)
>         unaryArrow (TypeVariable tv) =
>           do
>             alpha <- freshTypeVar
>             beta <- freshTypeVar
>             updateSt_ (bindVar tv (TypeArrow alpha beta))
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
>             updateSt_ (bindVar tv (TypeArrow beta gamma))
>             return (ty1,beta,gamma)
>         binaryArrow (ty1,ty2) =
>           errorAt p (nonBinaryOp what doc tcEnv (TypeArrow ty1 ty2))

\end{verbatim}
\paragraph{Unification}
The unification uses Robinson's algorithm (cf., e.g., Chap.~9
of~\cite{PeytonJones87:Book}).
\begin{verbatim}

> unify :: Position -> String -> Doc -> TCEnv -> Context -> Type
>       -> Context -> Type -> TcState Context
> unify p what doc tcEnv cx1 ty1 cx2 ty2 =
>   do
>     theta <- fetchSt
>     let ty1' = subst theta ty1
>     let ty2' = subst theta ty2
>     either (errorAt p . typeMismatch what doc tcEnv ty1' ty2')
>            (updateSt_ . compose)
>            (unifyTypes tcEnv ty1' ty2')
>     reduceContext p what doc tcEnv (cx1 ++ cx2)

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
>     theta <- fetchSt
>     iEnv <- liftM (apSnd3 (fmap (subst theta))) (liftSt fetchSt)
>     let cx' = subst theta cx
>         (cx1,cx2) =
>           partitionContext (minContext tcEnv (reduceTypePreds iEnv cx'))
>     theta' <- foldM (reportMissingInstance p what doc tcEnv iEnv) idSubst cx2
>     updateSt_ (compose theta')
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
>           fmap (map (expandAliasType tys) . snd3) (lookupEnv (CT cls tc) iEnv)
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
>         tys'
>           | length tys == length tys' -> return theta
>           | otherwise ->
>               liftM (flip (bindSubst tv) theta) (freshConstrained tys')
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
>     iEnv <- liftSt fetchSt
>     let theta =
>           foldr (bindDefault tcEnv iEnv cx) idSubst
>                 (nub [tv | TypePred cls (TypeVariable tv) <- cx,
>                            tv `notElemSet` fvs, isNumClass tcEnv cls])
>         cx' = fst (partitionContext (subst theta cx))
>         ty' = subst theta ty
>         tvs' = nub (filter (`notElemSet` fvs) (typeVars cx'))
>     unless (null tvs') (errorAt p (ambiguousType what doc tcEnv tvs' cx' ty'))
>     updateSt_ (compose theta)
>     return cx'

> bindDefault :: TCEnv -> InstEnv' -> [TypePred] -> Int -> TypeSubst
>             -> TypeSubst
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
Whenever type inference succeeds for a function equation, $($f$)$case
alternative, etc., which may open an existentially quantified data
type and thus bring fresh skolem constants into scope the compiler
checks that none of those skolem constants escape their scope through
the result type or the type environment. E.g., for the sample program
\begin{verbatim}
  data Key a = forall b. b (b -> a)
  f (Key x _) = x 
  g k x = fcase k of { Key _ f -> f x }
\end{verbatim}
a skolem constant escapes in the (result) type of \texttt{f} and in
the type of the environment variable \texttt{x} for the fcase
expression in the definition of \texttt{g}
(cf.~\cite{LauferOdersky94:AbstractTypes}).
\begin{verbatim}

> checkSkolems :: Position -> String -> (a -> Doc) -> TCEnv -> ValueEnv
>              -> Set Int -> Context -> Type -> a -> TcState (Context,Type,a)
> checkSkolems p what pp tcEnv tyEnv fs cx ty x =
>   do
>     theta <- fetchSt
>     let esc = filter escape $
>           [(v,subst theta ty) | (v,ty) <- (empty,QualType cx ty) : tys]
>     unless (null esc) (errorAt p (skolemEscapingScope tcEnv what (pp x) esc))
>     return (cx,ty,x)
>   where tys =
>           [(var v,ty) | (v,Value _ _ (ForAll _ ty)) <- localBindings tyEnv]
>         escape = any (`notElemSet` fs) . typeSkolems . snd
>         var v = text "Variable:" <+> ppIdent v

\end{verbatim}
\paragraph{Instantiation and Generalization}
We use negative offsets for fresh type variables.
\begin{verbatim}

> fresh :: (Int -> a) -> TcState a
> fresh f = liftM f (liftSt (liftSt (updateSt (1 +))))

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
> freshNumType = freshQualType [qNumId]
> freshFracType = freshQualType [qFractionalId]
> freshMonadType = freshQualType [qMonadId]

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

> skol :: TCEnv -> ([Ident],ConstrInfo,TypeScheme) -> TcState (Context,Type)
> skol tcEnv (_,ConstrInfo m cxR,ForAll n (QualType cx ty)) =
>   do
>     tys <- replicateM (n - m) freshTypeVar
>     tys' <- replicateM m freshSkolem
>     let tys'' = tys ++ tys'
>     liftSt (updateSt_ (apSnd3 (bindSkolemInsts tys'')))
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

> untyped :: Functor f => f a -> f QualType
> untyped = fmap (internalError "untyped")

\end{verbatim}
Error functions.
\begin{verbatim}

> inconsistentFieldLabel :: Ident -> String
> inconsistentFieldLabel l =
>   "Types for field label " ++ name l ++ " do not agree"

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

> skolemFieldLabel :: Ident -> String
> skolemFieldLabel l =
>   "Existential type escapes with type of record selector " ++ name l

> skolemEscapingScope :: TCEnv -> String -> Doc -> [(Doc,QualType)] -> String
> skolemEscapingScope tcEnv what doc esc = show $ vcat $
>   text "Existential type escapes out of its scope" :
>   sep [text what <> colon,indent doc] :
>   [whence $$ text "Type:" <+> ppQualType tcEnv ty | (whence,ty) <- esc]

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
