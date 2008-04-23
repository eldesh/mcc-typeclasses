% -*- LaTeX -*-
% $Id: KindCheck.lhs 2684 2008-04-23 17:46:29Z wlux $
%
% Copyright (c) 1999-2008, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{KindCheck.lhs}
\section{Kind Checking}
Before type checking, the compiler infers kinds for all type
constructors and type classes defined in the current module and
applies kind checking to the module's type signatures.
\begin{verbatim}

> module KindCheck(kindCheck,kindCheckGoal) where
> import Base
> import Combined
> import Curry
> import CurryPP
> import CurryUtils
> import Error
> import Kinds
> import KindSubst
> import KindTrans
> import List
> import Monad
> import Pretty
> import SCC
> import TopEnv
> import Types
> import TypeInfo
> import TypeTrans

> infixl 5 $-$

> ($-$) :: Doc -> Doc -> Doc
> x $-$ y = x $$ space $$ y

\end{verbatim}
In order to infer kinds for type constructors and type classes, the
compiler first sorts the module's type and class declarations into
minimal recursive binding groups and then applies kind inference to
each declaration group in turn. Besides inferring kinds for the type
constructors and type classes of a group, the compiler also checks
that there are no mutually recursive type synonym definitions and that
the super class hierarchy is acyclic. The former allows entering fully
expanded type synonyms into the type environment.
\begin{verbatim}

> kindCheck :: ModuleIdent -> TCEnv -> [TopDecl a] -> Error TCEnv
> kindCheck m tcEnv ds =
>   do
>     checkSynonyms m ds &&> checkSuperClasses m ds
>     tcEnv' <- foldM (kcDeclGroup m) tcEnv (scc bt (ft m) tds)
>     mapE_ (run . kcTopDecl m tcEnv') ods
>     return tcEnv'
>   where (tds,ods) = partition isTypeDecl ds

\end{verbatim}
Kind checking of a goal is simpler because there are no type
declarations.
\begin{verbatim}

> kindCheckGoal :: TCEnv -> Goal a -> Error ()
> kindCheckGoal tcEnv g = run $ kcGoal tcEnv g

\end{verbatim}
The kind checker uses a nested state transformer monad in order to
maintain the current substitution during kind inference and in order
to generate fresh kind variables.
\begin{verbatim}

> type KcState a = StateT KindSubst (StateT Int Error) a

> run :: KcState a -> Error a
> run m = callSt (callSt m idSubst) 1

\end{verbatim}
Minimal recursive declaration groups are computed using the sets of
bound and free type constructor and type class identifiers of the
declarations.
\begin{verbatim}

> bt :: TopDecl a -> [Ident]
> bt (DataDecl _ _ tc _ _ _) = [tc]
> bt (NewtypeDecl _ _ tc _ _ _) = [tc]
> bt (TypeDecl _ tc _ _) = [tc]
> bt (ClassDecl _ _ cls _ _) = [cls]
> bt (InstanceDecl _ _ _ _ _) = []
> bt (DefaultDecl _ tys) = []
> bt (BlockDecl _) = []

> ft :: ModuleIdent -> TopDecl a -> [Ident]
> ft m d = fts m d []

> class HasType a where
>   fts :: ModuleIdent -> a -> [Ident] -> [Ident]

> instance HasType a => HasType [a] where
>   fts m xs tcs = foldr (fts m) tcs xs

> instance HasType (TopDecl a) where
>   fts m (DataDecl _ cx _ _ cs clss) = fts m cx . fts m cs . fts m clss
>   fts m (NewtypeDecl _ cx _ _ nc clss) = fts m cx . fts m nc . fts m clss
>   fts m (TypeDecl _ _ _ ty) = fts m ty
>   fts m (ClassDecl _ cx _ _ ds) = fts m cx . fts m ds
>   fts m (InstanceDecl _ cx cls ty ds) =
>     fts m cx . fts m cls . fts m ty . fts m ds
>   fts m (DefaultDecl _ tys) = fts m tys
>   fts m (BlockDecl d) = fts m d

> instance HasType ConstrDecl where
>   fts m (ConstrDecl _ _ cx _ tys) = fts m cx . fts m tys
>   fts m (ConOpDecl _ _ cx ty1 _ ty2) = fts m cx . fts m ty1 . fts m ty2
>   fts m (RecordDecl _ _ cx _ fs) = fts m cx . fts m fs

> instance HasType FieldDecl where
>   fts m (FieldDecl _ _ ty) = fts m ty

> instance HasType NewConstrDecl where
>   fts m (NewConstrDecl _ _ ty) = fts m ty
>   fts m (NewRecordDecl _ _ _ ty) = fts m ty

> instance HasType (Decl a) where
>   fts _ (InfixDecl _ _ _ _) = id
>   fts m (TypeSig _ _ ty) = fts m ty
>   fts m (FunctionDecl _ _ eqs) = fts m eqs
>   fts m (ForeignDecl _ _ _ _ _ ty) = fts m ty
>   fts m (PatternDecl _ _ rhs) = fts m rhs
>   fts m (FreeDecl _ _) = id
>   fts _ (TrustAnnot _ _ _) = id

> instance HasType ClassAssert where
>   fts m (ClassAssert cls ty) = fts m cls . fts m ty

> instance HasType QualTypeExpr where
>   fts m (QualTypeExpr cx ty) = fts m cx . fts m ty

> instance HasType TypeExpr where
>   fts m (ConstructorType tc) = fts m tc
>   fts _ (VariableType _) = id
>   fts m (TupleType tys) = fts m tys
>   fts m (ListType ty) = fts m ty
>   fts m (ArrowType ty1 ty2) = fts m ty1 . fts m ty2
>   fts m (ApplyType ty1 ty2) = fts m ty1 . fts m ty2

> instance HasType (Equation a) where
>   fts m (Equation _ _ rhs) = fts m rhs

> instance HasType (Rhs a) where
>   fts m (SimpleRhs _ e ds) = fts m e . fts m ds
>   fts m (GuardedRhs es ds) = fts m es . fts m ds

> instance HasType (CondExpr a) where
>   fts m (CondExpr _ g e) = fts m g . fts m e

> instance HasType (Expression a) where
>   fts _ (Literal _ _) = id
>   fts _ (Variable _ _) = id
>   fts _ (Constructor _ _) = id
>   fts m (Paren e) = fts m e
>   fts m (Typed e ty) = fts m e . fts m ty
>   fts m (Record _ _ fs) = fts m fs
>   fts m (RecordUpdate e fs) = fts m e . fts m fs
>   fts m (Tuple es) = fts m es
>   fts m (List _ es) = fts m es
>   fts m (ListCompr e qs) = fts m e . fts m qs
>   fts m (EnumFrom e) = fts m e
>   fts m (EnumFromThen e1 e2) = fts m e1 . fts m e2
>   fts m (EnumFromTo e1 e2) = fts m e1 . fts m e2
>   fts m (EnumFromThenTo e1 e2 e3) = fts m e1 . fts m e2 . fts m e3
>   fts m (UnaryMinus e) = fts m e
>   fts m (Apply e1 e2) = fts m e1 . fts m e2
>   fts m (InfixApply e1 _ e2) = fts m e1 . fts m e2
>   fts m (LeftSection e _) = fts m e
>   fts m (RightSection _ e) = fts m e
>   fts m (Lambda _ _ e) = fts m e
>   fts m (Let ds e) = fts m ds . fts m e
>   fts m (Do sts e) = fts m sts . fts m e
>   fts m (IfThenElse e1 e2 e3) = fts m e1 . fts m e2 . fts m e3
>   fts m (Case e as) = fts m e . fts m as
>   fts m (Fcase e as) = fts m e . fts m as

> instance HasType (Statement a) where
>   fts m (StmtExpr e) = fts m e
>   fts m (StmtBind _ _ e) = fts m e
>   fts m (StmtDecl ds) = fts m ds

> instance HasType (Alt a) where
>   fts m (Alt _ _ rhs) = fts m rhs

> instance HasType a => HasType (Field a) where
>   fts m (Field _ x) = fts m x

> instance HasType QualIdent where
>   fts m x = maybe id (:) (localIdent m x)

\end{verbatim}
When synonym types are entered into the type environment, their right
hand sides are already fully expanded. This is possible because Curry
does not allow (mutually) recursive type synonyms, which is checked in
function \texttt{checkSynonyms} below. In addition, the compiler
checks that the super class hierarchy is acyclic (in function
\texttt{checkSuperClasses}).
\begin{verbatim}

> checkSynonyms :: ModuleIdent -> [TopDecl a] -> Error ()
> checkSynonyms m = mapE_ (typeDecl m) . scc bound free . filter isTypeDecl
>   where isTypeDecl (TypeDecl _ _ _ _) = True
>         isTypeDecl _ = False
>         bound (TypeDecl _ tc _ _) = [tc]
>         free (TypeDecl _ _ _ ty) = fts m ty []

> typeDecl :: ModuleIdent -> [TopDecl a] -> Error ()
> typeDecl _ [] = internalError "typeDecl"
> typeDecl m [TypeDecl p tc _ ty]
>   | tc `elem` fts m ty [] = errorAt p (recursiveTypes [tc])
>   | otherwise = return ()
> typeDecl _ (TypeDecl p tc _ _ : ds) =
>   errorAt p (recursiveTypes (tc : [tc' | TypeDecl _ tc' _ _ <- ds]))

> checkSuperClasses :: ModuleIdent -> [TopDecl a] -> Error ()
> checkSuperClasses m =
>   mapE_ (classDecl m) . scc bound free . filter isClassDecl
>   where bound (ClassDecl _ _ cls _ _) = [cls]
>         free (ClassDecl _ cx _ _ _) = fc m cx

> classDecl :: ModuleIdent -> [TopDecl a] -> Error ()
> classDecl _ [] = internalError "classDecl"
> classDecl m [ClassDecl p cx cls _ _]
>   | cls `elem` fc m cx = errorAt p (recursiveClasses [cls])
>   | otherwise = return ()
> classDecl _ (ClassDecl p _ cls _ _ : ds) =
>   errorAt p (recursiveClasses (cls : [cls' | ClassDecl _ _ cls' _ _ <- ds]))
> classDecl _ [d] = return ()

> fc :: ModuleIdent -> [ClassAssert] -> [Ident]
> fc m = foldr (\(ClassAssert cls _) -> maybe id (:) (localIdent m cls)) []

\end{verbatim}
For each declaration group, the kind checker first enters new
assumptions into the type environment. For a type constructor with
arity $n$, we enter kind $k_1 \rightarrow \dots \rightarrow k_n
\rightarrow k$, where $k_i$ are fresh type variables and $k$ is
$\star$ for data and newtype type constructors and a fresh type
variable for type synonym type constructors. For a type class we enter
kind $k$, where $k$ is a fresh type variable. Next, the kind checker
checks the declarations of the group within the extended environment,
and finally the kind checker instantiates all free kind variables to
$\star$ (cf.\ Sect.~4.6 of the revised Haskell'98
report~\cite{PeytonJones03:Haskell}).

As noted above, type synonyms are fully expanded while they are
entered into the type environment. Unfortunately, this requires either
sorting type synonym declarations properly or using the final type
environment for the expansion. We have chosen the latter option here.
Since recursive monadic bindings are not part of Haskell'98, we cannot
insert the correct alias type expansions in \texttt{bindKind}, but
have to do it while instantiating the remaining kind variables in
\texttt{bindDefaultKind}.

\ToDo{Simplify the implementation of \texttt{bindDefaultKind}. For
  instance, one could separate the conversion into the internal type
  representation and the expansion of aliases. Maybe one could even
  avoid alias expansion here and perform it on the fly during type
  inference. Using expanded alias types and mixing type conversion
  with alias expansion is just a relict from earlier compiler versions
  where the compiler could look up the definitions of only those type
  identifiers during type inference which are visible in the source
  code.}
\begin{verbatim}

> kcDeclGroup :: ModuleIdent -> TCEnv -> [TopDecl a] -> Error TCEnv
> kcDeclGroup m tcEnv ds = run $
>   do
>     tcEnv' <- foldM (bindKind m) tcEnv ds
>     mapM_ (kcTopDecl m tcEnv') ds
>     theta <- fetchSt
>     return (bindDefaultKinds m (fmap (subst theta) tcEnv') ds)
>   where ts = concatMap bt ds
>         bindDefaultKinds m tcEnv ds = tcEnv'
>           where tcEnv' = foldr (bindDefaultKind m tcEnv') tcEnv ds

> bindKind :: ModuleIdent -> TCEnv -> TopDecl a -> KcState TCEnv
> bindKind m tcEnv (DataDecl _ _ tc tvs cs _) =
>   bindTypeCon DataType m tc tvs (Just KindStar) (map constr cs) tcEnv
> bindKind m tcEnv (NewtypeDecl _ _ tc tvs nc _) =
>   bindTypeCon RenamingType m tc tvs (Just KindStar) (nconstr nc) tcEnv
> bindKind m tcEnv (TypeDecl _ tc tvs ty) =
>   bindTypeCon (flip AliasType (length tvs)) m tc tvs Nothing
>               (expandMonoType tcEnv tvs ty) tcEnv
> bindKind m tcEnv (ClassDecl _ cx cls tv ds) =
>   bindTypeClass m cls clss (concatMap methods ds) tcEnv
>   where QualType cx' _ =
>           expandPolyType tcEnv (QualTypeExpr cx (VariableType tv))
>         clss = [cls | TypePred cls _ <- cx']
> bindKind _ tcEnv (InstanceDecl _ _ _ _ _) = return tcEnv
> bindKind _ tcEnv (DefaultDecl _ _) = return tcEnv
> bindKind _ tcEnv (BlockDecl _) = return tcEnv

> bindTypeCon :: (QualIdent -> Kind -> a -> TypeInfo) -> ModuleIdent -> Ident
>             -> [Ident] -> Maybe Kind -> a -> TCEnv -> KcState TCEnv
> bindTypeCon f m tc tvs k x tcEnv =
>   do
>     k' <- maybe freshKindVar return k
>     ks <- mapM (const freshKindVar) tvs
>     return (globalBindTopEnv m tc (f tc' (foldr KindArrow k' ks) x) tcEnv)
>   where tc' = qualifyWith m tc

> bindTypeClass :: ModuleIdent -> Ident -> [QualIdent] -> [Ident] -> TCEnv
>               -> KcState TCEnv
> bindTypeClass m cls clss fs tcEnv =
>   do
>     k <- freshKindVar
>     return (globalBindTopEnv m cls (TypeClass cls' k clss fs) tcEnv)
>   where cls' = qualifyWith m cls

> bindDefaultKind :: ModuleIdent -> TCEnv -> TopDecl a -> TCEnv -> TCEnv
> bindDefaultKind m _ (DataDecl _ _ tc _ _ _) tcEnv =
>   case lookupTopEnv tc tcEnv of
>     DataType tc' k cs : _ ->
>       globalRebindTopEnv m tc (DataType tc' (defaultKind k) cs) tcEnv
>     _ -> internalError "bindDefaultKind (DataDecl)"
> bindDefaultKind m _ (NewtypeDecl _ _ tc _ _ _) tcEnv =
>   case lookupTopEnv tc tcEnv of
>     RenamingType tc' k nc : _ ->
>       globalRebindTopEnv m tc (RenamingType tc' (defaultKind k) nc) tcEnv
>     _ -> internalError "bindDefaultKind (RenamingDecl)"
> bindDefaultKind m tcEnv' (TypeDecl _ tc tvs ty) tcEnv =
>   case lookupTopEnv tc tcEnv of
>     AliasType tc' n k _ : _ ->
>       globalRebindTopEnv m tc (AliasType tc' n (defaultKind k) ty') tcEnv
>     _ -> internalError "bindDefaultKind (TypeDecl)"
>   where ty' = expandMonoType tcEnv' tvs ty
> bindDefaultKind m _ (ClassDecl _ _ cls _ _) tcEnv =
>   case lookupTopEnv cls tcEnv of
>     TypeClass cls' k clss fs : _ ->
>       globalRebindTopEnv m cls (TypeClass cls' (defaultKind k) clss fs) tcEnv
>     _ -> internalError "bindDefaultKind (ClassDecl)"
> bindDefaultKind _ _ (InstanceDecl _ _ _ _ _) tcEnv = tcEnv
> bindDefaultKind _ _ (DefaultDecl _ _) tcEnv = tcEnv
> bindDefaultKind _ _ (BlockDecl _) tcEnv = tcEnv

\end{verbatim}
After adding new assumptions to the environment, kind inference is
applied to all declarations. The type environment is extended
temporarily with bindings for the type variables occurring in the left
hand side of type declarations and the free type variables of type
signatures. While the kinds of the former are determined already by
the kinds of their type constructors and type classes, respectively
(see \texttt{bindKind} above), fresh kind variables are added for the
latter. Obviously, all types specified in a default declaration must
have kind $\star$.
\begin{verbatim}

> kcTopDecl :: ModuleIdent -> TCEnv -> TopDecl a -> KcState ()
> kcTopDecl m tcEnv (DataDecl p cx tc tvs cs _) =
>   kcContext tcEnv' p cx >> mapM_ (kcConstrDecl tcEnv') cs
>   where tcEnv' = snd (bindTypeVars m tc tvs tcEnv)
> kcTopDecl m tcEnv (NewtypeDecl p cx tc tvs nc _) =
>   kcContext tcEnv' p cx >> kcNewConstrDecl tcEnv' nc
>   where tcEnv' = snd (bindTypeVars m tc tvs tcEnv)
> kcTopDecl m tcEnv (TypeDecl p tc tvs ty) =
>   kcType tcEnv' p "type declaration" (ppTopDecl (TypeDecl p tc tvs ty)) k ty
>   where (k,tcEnv') = bindTypeVars m tc tvs tcEnv
> kcTopDecl m tcEnv (ClassDecl p cx cls tv ds) =
>   kcContext tcEnv' p cx >> mapM_ (kcDecl tcEnv' [tv]) ds
>   where tcEnv' = bindTypeVar tv (classKind (qualifyWith m cls) tcEnv) tcEnv
> kcTopDecl _ tcEnv (InstanceDecl p cx cls ty ds) =
>   do
>     tcEnv' <- foldM bindFreshKind tcEnv (fv ty)
>     kcContext tcEnv' p cx
>     kcType tcEnv' p "instance declaration" doc (classKind cls tcEnv) ty
>     mapM_ (kcDecl tcEnv []) ds
>   where doc = ppTopDecl (InstanceDecl p cx cls ty [])
> kcTopDecl _ tcEnv (DefaultDecl p tys) =
>   do
>     tcEnv' <- foldM bindFreshKind tcEnv (nub (fv tys))
>     mapM_ (kcValueType tcEnv' p "default declaration" empty) tys
> kcTopDecl _ tcEnv (BlockDecl d) = kcDecl tcEnv [] d

> bindTypeVars :: ModuleIdent -> Ident -> [Ident] -> TCEnv -> (Kind,TCEnv)
> bindTypeVars m tc tvs tcEnv =
>   foldl (\(KindArrow k1 k2,tcEnv) tv -> (k2,bindTypeVar tv k1 tcEnv))
>         (constrKind (qualifyWith m tc) tcEnv,tcEnv)
>         tvs

> bindTypeVar :: Ident -> Kind -> TCEnv -> TCEnv
> bindTypeVar tv k = localBindTopEnv tv (TypeVar k)

> bindFreshKind :: TCEnv -> Ident -> KcState TCEnv
> bindFreshKind tcEnv tv =
>   do
>     k <- freshKindVar
>     return (bindTypeVar tv k tcEnv)

> kcGoal :: TCEnv -> Goal a -> KcState ()
> kcGoal tcEnv (Goal p e ds) = kcExpr tcEnv p e >> mapM_ (kcDecl tcEnv []) ds

> kcDecl :: TCEnv -> [Ident] -> Decl a -> KcState ()
> kcDecl _ _ (InfixDecl _ _ _ _) = return ()
> kcDecl tcEnv tvs (TypeSig p _ ty) = kcTypeSig tcEnv tvs p ty
> kcDecl tcEnv _ (FunctionDecl _ _ eqs) = mapM_ (kcEquation tcEnv) eqs
> kcDecl tcEnv tvs (ForeignDecl p _ _ _ _ ty) =
>   kcTypeSig tcEnv tvs p (QualTypeExpr [] ty)
> kcDecl tcEnv _ (PatternDecl _ _ rhs) = kcRhs tcEnv rhs
> kcDecl _ _ (FreeDecl _ _) = return ()
> kcDecl _ _ (TrustAnnot _ _ _) = return ()

> kcConstrDecl :: TCEnv -> ConstrDecl -> KcState ()
> kcConstrDecl tcEnv d@(ConstrDecl p evs cx _ tys) =
>   do
>     tcEnv' <- foldM bindFreshKind tcEnv evs
>     kcContext tcEnv' p cx
>     mapM_ (kcValueType tcEnv' p what doc) tys
>   where what = "data constructor declaration"
>         doc = ppConstr d
> kcConstrDecl tcEnv d@(ConOpDecl p evs cx ty1 _ ty2) =
>   do
>     tcEnv' <- foldM bindFreshKind tcEnv evs
>     kcContext tcEnv' p cx
>     kcValueType tcEnv' p what doc ty1
>     kcValueType tcEnv' p what doc ty2
>   where what = "data constructor declaration"
>         doc = ppConstr d
> kcConstrDecl tcEnv (RecordDecl p evs cx _ fs) =
>   do
>     tcEnv' <- foldM bindFreshKind tcEnv evs
>     kcContext tcEnv' p cx
>     mapM_ (kcFieldDecl tcEnv') fs

> kcFieldDecl :: TCEnv -> FieldDecl -> KcState ()
> kcFieldDecl tcEnv d@(FieldDecl p _ ty) =
>   kcValueType tcEnv p "labeled declaration" (ppFieldDecl d) ty

> kcNewConstrDecl :: TCEnv -> NewConstrDecl -> KcState ()
> kcNewConstrDecl tcEnv d@(NewConstrDecl p _ ty) =
>   kcValueType tcEnv p "newtype constructor declaration" (ppNewConstr d) ty
> kcNewConstrDecl tcEnv (NewRecordDecl p _ l ty) =
>   kcFieldDecl tcEnv (FieldDecl p [l] ty)

> kcEquation :: TCEnv -> Equation a -> KcState ()
> kcEquation tcEnv (Equation _ _ rhs) = kcRhs tcEnv rhs

> kcRhs :: TCEnv -> Rhs a -> KcState ()
> kcRhs tcEnv (SimpleRhs p e ds) =
>   kcExpr tcEnv p e >> mapM_ (kcDecl tcEnv []) ds
> kcRhs tcEnv (GuardedRhs es ds) =
>   mapM_ (kcCondExpr tcEnv) es >> mapM_ (kcDecl tcEnv []) ds

> kcCondExpr :: TCEnv -> CondExpr a -> KcState ()
> kcCondExpr tcEnv (CondExpr p g e) = kcExpr tcEnv p g >> kcExpr tcEnv p e

> kcExpr :: TCEnv -> Position -> Expression a -> KcState ()
> kcExpr _ _ (Literal _ _) = return ()
> kcExpr _ _ (Variable _ _) = return ()
> kcExpr _ _ (Constructor _ _) = return ()
> kcExpr tcEnv p (Paren e) = kcExpr tcEnv p e
> kcExpr tcEnv p (Typed e ty) = kcExpr tcEnv p e >> kcTypeSig tcEnv [] p ty
> kcExpr tcEnv p (Record _ _ fs) = mapM_ (kcField tcEnv p) fs
> kcExpr tcEnv p (RecordUpdate e fs) =
>   kcExpr tcEnv p e >> mapM_ (kcField tcEnv p) fs
> kcExpr tcEnv p (Tuple es) = mapM_ (kcExpr tcEnv p) es
> kcExpr tcEnv p (List _ es) = mapM_ (kcExpr tcEnv p) es
> kcExpr tcEnv p (ListCompr e qs) =
>   kcExpr tcEnv p e >> mapM_ (kcStmt tcEnv p) qs
> kcExpr tcEnv p (EnumFrom e) = kcExpr tcEnv p e
> kcExpr tcEnv p (EnumFromThen e1 e2) = kcExpr tcEnv p e1 >> kcExpr tcEnv p e2
> kcExpr tcEnv p (EnumFromTo e1 e2) = kcExpr tcEnv p e1 >> kcExpr tcEnv p e2
> kcExpr tcEnv p (EnumFromThenTo e1 e2 e3) =
>   kcExpr tcEnv p e1 >> kcExpr tcEnv p e2 >> kcExpr tcEnv p e3
> kcExpr tcEnv p (UnaryMinus e) = kcExpr tcEnv p e
> kcExpr tcEnv p (Apply e1 e2) = kcExpr tcEnv p e1 >> kcExpr tcEnv p e2
> kcExpr tcEnv p (InfixApply e1 _ e2) = kcExpr tcEnv p e1 >> kcExpr tcEnv p e2
> kcExpr tcEnv p (LeftSection e _) = kcExpr tcEnv p e
> kcExpr tcEnv p (RightSection _ e) = kcExpr tcEnv p e
> kcExpr tcEnv _ (Lambda p _ e) = kcExpr tcEnv p e
> kcExpr tcEnv p (Let ds e) = mapM_ (kcDecl tcEnv []) ds >> kcExpr tcEnv p e
> kcExpr tcEnv p (Do sts e) = mapM_ (kcStmt tcEnv p) sts >> kcExpr tcEnv p e
> kcExpr tcEnv p (IfThenElse e1 e2 e3) =
>   kcExpr tcEnv p e1 >> kcExpr tcEnv p e2 >> kcExpr tcEnv p e3
> kcExpr tcEnv p (Case e alts) = kcExpr tcEnv p e >> mapM_ (kcAlt tcEnv) alts
> kcExpr tcEnv p (Fcase e alts) = kcExpr tcEnv p e >> mapM_ (kcAlt tcEnv) alts

> kcStmt :: TCEnv -> Position -> Statement a -> KcState ()
> kcStmt tcEnv p (StmtExpr e) = kcExpr tcEnv p e
> kcStmt tcEnv _ (StmtBind p _ e) = kcExpr tcEnv p e
> kcStmt tcEnv _ (StmtDecl ds) = mapM_ (kcDecl tcEnv []) ds

> kcAlt :: TCEnv -> Alt a -> KcState ()
> kcAlt tcEnv (Alt _ _ rhs) = kcRhs tcEnv rhs

> kcField :: TCEnv -> Position -> Field (Expression a) -> KcState ()
> kcField tcEnv p (Field _ e) = kcExpr tcEnv p e

> kcTypeSig :: TCEnv -> [Ident] -> Position -> QualTypeExpr -> KcState ()
> kcTypeSig tcEnv tvs p (QualTypeExpr cx ty) =
>   do
>     tcEnv' <- foldM bindFreshKind tcEnv (filter (`notElem` tvs) (nub (fv ty)))
>     kcContext tcEnv' p cx
>     kcValueType tcEnv' p "type signature" doc ty
>   where doc = ppQualTypeExpr (QualTypeExpr cx ty)

> kcContext :: TCEnv -> Position -> [ClassAssert] -> KcState ()
> kcContext tcEnv p = mapM_ (kcClassAssert tcEnv p)

> kcClassAssert :: TCEnv -> Position -> ClassAssert -> KcState ()
> kcClassAssert tcEnv p (ClassAssert cls ty) =
>   kcType tcEnv p "class constraint" doc (classKind cls tcEnv) ty
>   where doc = ppClassAssert (ClassAssert cls ty)

> kcValueType :: TCEnv -> Position -> String -> Doc -> TypeExpr -> KcState ()
> kcValueType tcEnv p what doc = kcType tcEnv p what doc KindStar

> kcType :: TCEnv -> Position -> String -> Doc -> Kind -> TypeExpr -> KcState ()
> kcType tcEnv p what doc k ty =
>   kcTypeExpr tcEnv p "type expression" doc' 0 ty >>=
>     unify p what (doc $-$ text "Type:" <+> doc') k
>   where doc' = ppTypeExpr 0 ty

> kcTypeExpr :: TCEnv -> Position -> String -> Doc -> Int -> TypeExpr
>            -> KcState Kind
> kcTypeExpr tcEnv p _ _ n (ConstructorType tc) =
>   case aliasArity tc tcEnv of
>     Just n'
>       | n >= n' -> return (constrKind tc tcEnv)
>       | otherwise -> errorAt p (partialAlias tc n' n)
>     Nothing -> return (constrKind tc tcEnv)
> kcTypeExpr tcEnv _ _ _ _ (VariableType tv) = return (varKind tv tcEnv)
> kcTypeExpr tcEnv p what doc _ (TupleType tys) =
>   do
>     mapM_ (kcValueType tcEnv p what doc) tys
>     return KindStar
> kcTypeExpr tcEnv p what doc _ (ListType ty) =
>   do
>     kcValueType tcEnv p what doc ty
>     return KindStar
> kcTypeExpr tcEnv p what doc _ (ArrowType ty1 ty2) =
>   do
>     kcValueType tcEnv p what doc ty1
>     kcValueType tcEnv p what doc ty2
>     return KindStar
> kcTypeExpr tcEnv p what doc n (ApplyType ty1 ty2) =
>   do
>     (alpha,beta) <-
>       kcTypeExpr tcEnv p what doc (n + 1) ty1 >>=
>       kcArrow p what (doc $-$ text "Type:" <+> ppTypeExpr 0 ty1)
>     kcTypeExpr tcEnv p what doc 0 ty2 >>=
>       unify p what (doc $-$ text "Type:" <+> ppTypeExpr 0 ty2) alpha
>     return beta

\end{verbatim}
The function \texttt{kcArrow} checks that its argument can be used as
an arrow kind $\alpha\rightarrow\beta$ and returns the pair
$(\alpha,\beta)$.
\begin{verbatim}

> kcArrow :: Position -> String -> Doc -> Kind -> KcState (Kind,Kind)
> kcArrow p what doc k =
>   do
>     theta <- fetchSt
>     case subst theta k of
>       KindStar -> errorAt p (nonArrowKind what doc KindStar)
>       KindVariable kv ->
>         do
>           alpha <- freshKindVar
>           beta <- freshKindVar
>           updateSt_ (bindVar kv (KindArrow alpha beta))
>           return (alpha,beta)
>       KindArrow k1 k2 -> return (k1,k2)

\end{verbatim}
Unification uses Robinson's algorithm (cf., e.g., Chap.~9
of~\cite{PeytonJones87:Book}).
\begin{verbatim}

> unify :: Position -> String -> Doc -> Kind -> Kind -> KcState ()
> unify p what doc k1 k2 =
>   do
>     theta <- fetchSt
>     let k1' = subst theta k1
>     let k2' = subst theta k2
>     maybe (errorAt p (kindMismatch what doc k1' k2'))
>           (updateSt_ . compose)
>           (unifyKinds k1' k2')

> unifyKinds :: Kind -> Kind -> Maybe KindSubst
> unifyKinds (KindVariable kv1) (KindVariable kv2)
>   | kv1 == kv2 = Just idSubst
>   | otherwise = Just (bindSubst kv1 (KindVariable kv2) idSubst)
> unifyKinds (KindVariable kv) k
>   | kv `elem` kindVars k = Nothing
>   | otherwise = Just (bindSubst kv k idSubst)
> unifyKinds k (KindVariable kv)
>   | kv `elem` kindVars k = Nothing
>   | otherwise = Just (bindSubst kv k idSubst)
> unifyKinds KindStar KindStar = Just idSubst
> unifyKinds (KindArrow k11 k12) (KindArrow k21 k22) =
>   do
>     theta <- unifyKinds k11 k21
>     theta' <- unifyKinds (subst theta k12) (subst theta k22)
>     Just (compose theta' theta)
> unifyKinds _ _ = Nothing

\end{verbatim}
Fresh variables.
\begin{verbatim}

> fresh :: (Int -> a) -> KcState a
> fresh f = liftM f (liftSt (updateSt (1 +)))

> freshKindVar :: KcState Kind
> freshKindVar = fresh KindVariable

\end{verbatim}
Error messages.
\begin{verbatim}

> recursiveTypes :: [Ident] -> String
> recursiveTypes [tc] = "Recursive type synonym " ++ name tc
> recursiveTypes (tc:tcs) =
>   "Mutually recursive type synonyms " ++ name tc ++ types "" tcs
>   where types comma [tc] = comma ++ " and " ++ name tc
>         types _ (tc:tcs) = ", " ++ name tc ++ types "," tcs

> recursiveClasses :: [Ident] -> String
> recursiveClasses [tc] = "Recursive type class " ++ name tc
> recursiveClasses (tc:tcs) =
>   "Mutually recursive type classes " ++ name tc ++ types "" tcs
>   where types comma [tc] = comma ++ " and " ++ name tc
>         types _ (tc:tcs) = ", " ++ name tc ++ types "," tcs

> nonArrowKind :: String -> Doc -> Kind -> String
> nonArrowKind what doc k = show $
>   vcat [text "Kind error in" <+> text what, doc,
>         text "Kind:" <+> ppKind k,
>         text "Cannot be applied"]

> kindMismatch :: String -> Doc -> Kind -> Kind -> String
> kindMismatch what doc k1 k2 = show $
>   vcat [text "Kind error in" <+> text what, doc,
>         text "Inferred kind:" <+> ppKind k2,
>         text "Expected kind:" <+> ppKind k1]

> partialAlias :: QualIdent -> Int -> Int -> String
> partialAlias tc arity argc = show $
>   hsep [text "Type synonym", ppQIdent tc, text "requires at least",
>         int arity, text (plural arity "argument") <> comma,
>         text "but is applied to only", int argc]
>   where plural n x = if n == 1 then x else x ++ "s"

\end{verbatim}
