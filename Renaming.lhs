% -*- LaTeX -*-
% $Id: Renaming.lhs 3056 2011-10-07 16:27:03Z wlux $
%
% Copyright (c) 1999-2011, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Renaming.lhs}
\section{Renaming}
After checking for syntax errors, the compiler renames all type
variables and all \emph{local} variables in expressions. This renaming
allows the compiler to pass on type information to later phases in a
flat environment, and also makes lifting of declarations simpler.
Renaming is performed by adding a unique key to each renamed variable.
Global variables are not renamed so that no renamed variables occur in
module interfaces. Since no name conflicts are possible within a
declaration group, the same key can be used for all identifiers
declared in that group. Nevertheless, a fresh key must be generated
for each anonymous variable.

Note that this pass deliberately \emph{does not} qualify the names of
imported functions and constructors. This qualification will be done
after type checking was performed.
\begin{verbatim}

> module Renaming(Key,k0,rename,renameGoal) where
> import Base
> import Combined
> import Curry
> import Env
> import Maybe
> import Monad
> import Utils

\end{verbatim}
Since only type and local variables are renamed, it is sufficient to
use an environment mapping unqualified identifiers onto their new
names.
\begin{verbatim}

> type RenameEnv = Env Ident Ident

> bindVar :: Int -> Ident -> RenameEnv -> RenameEnv
> bindVar k x = bindEnv x (renameIdent x k)

> lookupVar :: Ident -> RenameEnv -> Maybe Ident
> lookupVar = lookupEnv

\end{verbatim}
In order to thread the counter used for generating unique keys, we use
a simple state monad. Since renaming is applied independently to
source code declarations and derived instance declarations, the
counter's value must be returned from the state monad when renaming is
finished and used as new initial state upon the next invocation of the
renaming state monad. The global variable \texttt{k0} provides the
initial counter value for the first invocation of the renaming state
monad. We use the private \texttt{Key} type in order to hide the
counter's representation from client modules.
\begin{verbatim}

> newtype Key = Key Int
> type RenameState a = StateT Int Id a

> run :: RenameState a -> Key -> (Key,a)
> run m (Key k) = runSt (m >>= \x -> fetchSt >>= \k' -> return (Key k',x)) k

> k0 :: Key
> k0 = Key (globalKey + 1)

> globalKey :: Int
> globalKey = uniqueId (mkIdent "")

\end{verbatim}
New variable bindings are introduced at the level of declaration
groups and argument lists.
\begin{verbatim}

> bindVars :: RenameEnv -> [Ident] -> RenameState RenameEnv
> bindVars env xs = liftM (\k -> foldr (bindVar k) env xs) (updateSt (1 +))

\end{verbatim}
The function \texttt{renameVar} renames an identifier. When applied to
an anonymous identifier, a fresh index is used to rename it. For all
other identifiers, \texttt{renameVar} checks whether a binding is
present in the current renaming environment and returns that binding.
Otherwise, the unmodified identifier is returned.

As all qualified identifiers refer to top-level entities (either
defined in the current module or imported from another module),
\texttt{renameQual} applies renaming only to identifiers without a
module qualifier.
\begin{verbatim}

> renameVar :: RenameEnv -> Ident -> RenameState Ident
> renameVar env x
>   | x == anonId = liftM (renameIdent x) (updateSt (1 +))
>   | otherwise = return (fromMaybe x (lookupVar x env))

> renameQual :: RenameEnv -> QualIdent -> RenameState QualIdent
> renameQual env x
>   | isJust m = return x
>   | otherwise = liftM qualify (renameVar env x')
>   where (m,x') = splitQualIdent x

\end{verbatim}
The renaming pass simply descends into the structure of the abstract
syntax tree and renames all type and expression variables.
\begin{verbatim}

> rename :: Key -> [TopDecl a] -> (Key,[TopDecl a])
> rename k ds = run (mapM renameTopDecl ds) k

> renameGoal :: Key -> Goal a -> (Key,Goal a)
> renameGoal k (Goal p e ds) = flip run k $
>   do
>     env' <- bindVars emptyEnv (bv ds)
>     ds' <- mapM (renameDecl env') ds
>     e' <- renameExpr env' e
>     return (Goal p e' ds')

> renameTopDecl :: TopDecl a -> RenameState (TopDecl a)
> renameTopDecl (DataDecl p cx tc tvs cs clss) =
>   do
>     env <- bindVars emptyEnv tvs
>     cx' <- mapM (renameClassAssert env) cx
>     tvs' <- mapM (renameVar env) tvs
>     cs' <- mapM (renameConstrDecl env) cs
>     return (DataDecl p cx' tc tvs' cs' clss)
> renameTopDecl (NewtypeDecl p cx tc tvs nc clss) =
>   do
>     env <- bindVars emptyEnv tvs
>     cx' <- mapM (renameClassAssert env) cx
>     tvs' <- mapM (renameVar env) tvs
>     nc' <- renameNewConstrDecl env nc
>     return (NewtypeDecl p cx' tc tvs' nc' clss)
> renameTopDecl (TypeDecl p tc tvs ty) =
>   do
>     env <- bindVars emptyEnv tvs
>     liftM2 (TypeDecl p tc) (mapM (renameVar env) tvs) (renameType env ty)
> renameTopDecl (ClassDecl p cx cls tv ds) =
>   do
>     env <- bindVars emptyEnv [tv]
>     env' <- bindVars emptyEnv [f | FunctionDecl _ _ f _ <- ds]
>     liftM3 (flip (ClassDecl p) cls)
>            (mapM (renameClassAssert env) cx)
>            (renameVar env tv)
>            (mapM (renameMethodDecl env env') ds)
> renameTopDecl (InstanceDecl p cx cls ty ds) =
>   do
>     env <- bindVars emptyEnv (fv ty)
>     env' <- bindVars emptyEnv [f | FunctionDecl _ _ f _ <- ds]
>     liftM3 (flip (InstanceDecl p) cls)
>            (mapM (renameClassAssert env) cx)
>            (renameType env ty)
>            (mapM (renameMethodDecl emptyEnv env') ds)
> renameTopDecl (DefaultDecl p tys) =
>   do
>     tys' <- mapM (renameTypeSig emptyEnv . QualTypeExpr []) tys
>     return (DefaultDecl p [ty | QualTypeExpr _ ty <- tys'])
> renameTopDecl (BlockDecl d) = liftM BlockDecl (renameDecl emptyEnv d)

> renameConstrDecl :: RenameEnv -> ConstrDecl -> RenameState ConstrDecl
> renameConstrDecl env (ConstrDecl p evs cx c tys) =
>   do
>     env' <- bindVars env evs
>     evs' <- mapM (renameVar env') evs
>     cx' <- mapM (renameClassAssert env') cx
>     tys' <- mapM (renameType env') tys
>     return (ConstrDecl p evs' cx' c tys')
> renameConstrDecl env (ConOpDecl p evs cx ty1 op ty2) =
>   do
>     env' <- bindVars env evs
>     evs' <- mapM (renameVar env') evs
>     cx' <- mapM (renameClassAssert env') cx
>     ty1' <- renameType env' ty1
>     ty2' <- renameType env' ty2
>     return (ConOpDecl p evs' cx' ty1' op ty2')
> renameConstrDecl env (RecordDecl p evs cx c fs) =
>   do
>     env' <- bindVars env evs
>     evs' <- mapM (renameVar env') evs
>     cx' <- mapM (renameClassAssert env') cx
>     fs' <- mapM (renameFieldDecl env') fs
>     return (RecordDecl p evs' cx' c fs')

> renameFieldDecl :: RenameEnv -> FieldDecl -> RenameState FieldDecl
> renameFieldDecl env (FieldDecl p ls ty) =
>   liftM (FieldDecl p ls) (renameType env ty)

> renameNewConstrDecl :: RenameEnv -> NewConstrDecl -> RenameState NewConstrDecl
> renameNewConstrDecl env (NewConstrDecl p c ty) =
>   liftM (NewConstrDecl p c) (renameType env ty)
> renameNewConstrDecl env (NewRecordDecl p c l ty) =
>   liftM (NewRecordDecl p c l) (renameType env ty)

\end{verbatim}
When renaming class and instance declarations, the compiler renames
method identifiers in the left hand side of method implementations,
but does not change method identifiers that occur in the right hand
sides (nor in type signatures and fixity declarations). This nicely
reflects the fact that the method identifier in the left hand side
denotes a particular method implementation, whereas any occurrence of
a method identifier in the right hand side denotes the overloaded type
class method.
\begin{verbatim}

> renameMethodDecl :: RenameEnv -> RenameEnv -> Decl a -> RenameState (Decl a)
> renameMethodDecl _ _ (InfixDecl p fix pr ops) =
>   return (InfixDecl p fix pr ops)
> renameMethodDecl env _ (TypeSig p fs ty) =
>   liftM (TypeSig p fs) (renameTypeSig env ty)
> renameMethodDecl _ env' (FunctionDecl p a f eqs) =
>   do
>     f' <- renameVar env' f
>     liftM (FunctionDecl p a f') (mapM (renameEqn f' emptyEnv) eqs)
> renameMethodDecl _ env' (TrustAnnot p tr fs) =
>   liftM (TrustAnnot p tr) (mapM (renameVar env') fs)

> renameTypeSig :: RenameEnv -> QualTypeExpr -> RenameState QualTypeExpr
> renameTypeSig env ty =
>   do
>     env' <- bindVars env (filter (`notElem` tvs) (fv ty))
>     renameQualType env' ty
>   where tvs = map fst (envToList env)

> renameQualType :: RenameEnv -> QualTypeExpr -> RenameState QualTypeExpr
> renameQualType env (QualTypeExpr cx ty) =
>   liftM2 QualTypeExpr (mapM (renameClassAssert env) cx) (renameType env ty)

> renameClassAssert :: RenameEnv -> ClassAssert -> RenameState ClassAssert
> renameClassAssert env (ClassAssert cls ty) =
>   liftM (ClassAssert cls) (renameType env ty)

> renameType :: RenameEnv -> TypeExpr -> RenameState TypeExpr
> renameType _ (ConstructorType tc) = return (ConstructorType tc)
> renameType env (VariableType tv) = liftM VariableType (renameVar env tv)
> renameType env (TupleType tys) = liftM TupleType (mapM (renameType env) tys)
> renameType env (ListType ty) = liftM ListType (renameType env ty)
> renameType env (ArrowType ty1 ty2) =
>   liftM2 ArrowType (renameType env ty1) (renameType env ty2)
> renameType env (ApplyType ty1 ty2) =
>   liftM2 ApplyType (renameType env ty1) (renameType env ty2)

> renameDecl :: RenameEnv -> Decl a -> RenameState (Decl a)
> renameDecl env (InfixDecl p fix pr ops) =
>   liftM (InfixDecl p fix pr) (mapM (renameVar env) ops)
> renameDecl env (TypeSig p fs ty) =
>   liftM2 (TypeSig p) (mapM (renameVar env) fs) (renameTypeSig emptyEnv ty)
> renameDecl env (FunctionDecl p a f eqs) =
>   do
>     f' <- renameVar env f
>     liftM (FunctionDecl p a f') (mapM (renameEqn f' env) eqs)
> renameDecl env (ForeignDecl p fi a f ty) =
>   do
>     f' <- renameVar env f
>     QualTypeExpr _ ty' <- renameTypeSig emptyEnv (QualTypeExpr [] ty)
>     return (ForeignDecl p fi a f' ty')
> renameDecl env (PatternDecl p t rhs) =
>   liftM2 (PatternDecl p) (renameConstrTerm env env t) (renameRhs env rhs)
> renameDecl env (FreeDecl p vs) =
>   liftM (FreeDecl p) (mapM (renameFreeVar env) vs)
> renameDecl env (TrustAnnot p t fs) =
>   liftM (TrustAnnot p t) (mapM (renameVar env) fs)

> renameFreeVar :: RenameEnv -> FreeVar a -> RenameState (FreeVar a)
> renameFreeVar env (FreeVar a v) = liftM (FreeVar a) (renameVar env v)

\end{verbatim}
Note that the root of the left hand side term of an equation must be
equal to the name of the function declaration. This means that we must
not rename this identifier in the same environment as its arguments.
Similarly, we must be careful with function patterns. For instance,
given the (contrived) definition \texttt{f (id id x) = x}, the
argument is considered a function pattern with the first occurrence of
\texttt{id} referring to the global definition of \texttt{Prelude.id}.
The second occurrence of \texttt{id} in the function pattern
introduces a local variable that shadows the global function.
Nevertheless, the first occurrence of \texttt{id} must not be renamed.
For that reason, \texttt{renameLhs} and \texttt{renameConstrTerm} are
applied to two renaming environments. The first is the global
environment in which the function is defined and the second is the
local environment, which includes the function's arguments. Obviously,
the same environment is used for both arguments in case of pattern
declarations.
\begin{verbatim}

> renameEqn :: Ident -> RenameEnv -> Equation a -> RenameState (Equation a)
> renameEqn f env (Equation p lhs rhs) =
>   do
>     env' <- bindVars env (bv lhs)
>     liftM2 (Equation p) (renameLhs f env env' lhs) (renameRhs env' rhs)

> renameLhs :: Ident -> RenameEnv -> RenameEnv -> Lhs a -> RenameState (Lhs a)
> renameLhs f env env' (FunLhs _ ts) =
>   liftM (FunLhs f) (mapM (renameConstrTerm env env') ts)
> renameLhs f env env' (OpLhs t1 _ t2) =
>   liftM2 (flip OpLhs f)
>          (renameConstrTerm env env' t1)
>          (renameConstrTerm env env' t2)
> renameLhs f env env' (ApLhs lhs ts) =
>   liftM2 ApLhs
>          (renameLhs f env env' lhs)
>          (mapM (renameConstrTerm env env') ts)

> renameRhs :: RenameEnv -> Rhs a -> RenameState (Rhs a)
> renameRhs env (SimpleRhs p e ds) =
>   do
>     env' <- bindVars env (bv ds)
>     ds' <- mapM (renameDecl env') ds
>     e' <- renameExpr env' e
>     return (SimpleRhs p e' ds')
> renameRhs env (GuardedRhs es ds) =
>   do
>     env' <- bindVars env (bv ds)
>     ds' <- mapM (renameDecl env') ds
>     es' <- mapM (renameCondExpr env') es
>     return (GuardedRhs es' ds')

> renameConstrTerm :: RenameEnv -> RenameEnv -> ConstrTerm a
>                  -> RenameState (ConstrTerm a)
> renameConstrTerm _ _ (LiteralPattern a l) = return (LiteralPattern a l)
> renameConstrTerm _ _ (NegativePattern a l) = return (NegativePattern a l)
> renameConstrTerm _ env' (VariablePattern a x) =
>   liftM (VariablePattern a) (renameVar env' x)
> renameConstrTerm env env' (ConstructorPattern a c ts) =
>   liftM (ConstructorPattern a c) (mapM (renameConstrTerm env env') ts)
> renameConstrTerm env env' (FunctionPattern a f ts) =
>   liftM2 (FunctionPattern a)
>          (renameQual env f)
>          (mapM (renameConstrTerm env env') ts)
> renameConstrTerm env env' (InfixPattern a t1 op t2) =
>   liftM3 (InfixPattern a)
>          (renameConstrTerm env env' t1)
>          (renameOp env op)
>          (renameConstrTerm env env' t2)
> renameConstrTerm env env' (ParenPattern t) =
>   liftM ParenPattern (renameConstrTerm env env' t)
> renameConstrTerm env env' (RecordPattern a c fs) =
>   liftM (RecordPattern a c)
>         (mapM (renameField (renameConstrTerm env env')) fs)
> renameConstrTerm env env' (TuplePattern ts) =
>   liftM TuplePattern (mapM (renameConstrTerm env env') ts)
> renameConstrTerm env env' (ListPattern a ts) =
>   liftM (ListPattern a) (mapM (renameConstrTerm env env') ts)
> renameConstrTerm env env' (AsPattern x t) =
>   liftM2 AsPattern (renameVar env' x) (renameConstrTerm env env' t)
> renameConstrTerm env env' (LazyPattern t) =
>   liftM LazyPattern (renameConstrTerm env env' t)

> renameCondExpr :: RenameEnv -> CondExpr a -> RenameState (CondExpr a)
> renameCondExpr env (CondExpr p g e) =
>   liftM2 (CondExpr p) (renameExpr env g) (renameExpr env e)

> renameExpr :: RenameEnv -> Expression a -> RenameState (Expression a)
> renameExpr _ (Literal a l) = return (Literal a l)
> renameExpr env (Variable a x) = liftM (Variable a) (renameQual env x)
> renameExpr _ (Constructor a c) = return (Constructor a c)
> renameExpr env (Paren e) = liftM Paren (renameExpr env e)
> renameExpr env (Typed e ty) =
>   liftM2 Typed (renameExpr env e) (renameTypeSig emptyEnv ty)
> renameExpr env (Record a c fs) =
>   liftM (Record a c) (mapM (renameField (renameExpr env)) fs)
> renameExpr env (RecordUpdate e fs) =
>   liftM2 RecordUpdate
>          (renameExpr env e)
>          (mapM (renameField (renameExpr env)) fs)
> renameExpr env (Tuple es) = liftM Tuple (mapM (renameExpr env) es)
> renameExpr env (List a es) = liftM (List a) (mapM (renameExpr env) es)
> renameExpr env (ListCompr e qs) =
>   do
>     (env',qs') <- mapAccumM renameStmt env qs
>     e' <- renameExpr env' e
>     return (ListCompr e' qs')
> renameExpr env (EnumFrom e) = liftM EnumFrom (renameExpr env e)
> renameExpr env (EnumFromThen e1 e2) =
>   liftM2 EnumFromThen (renameExpr env e1) (renameExpr env e2)
> renameExpr env (EnumFromTo e1 e2) =
>   liftM2 EnumFromTo (renameExpr env e1) (renameExpr env e2)
> renameExpr env (EnumFromThenTo e1 e2 e3) =
>   liftM3 EnumFromThenTo
>          (renameExpr env e1)
>          (renameExpr env e2)
>          (renameExpr env e3)
> renameExpr env (UnaryMinus e) = liftM UnaryMinus (renameExpr env e)
> renameExpr env (Apply e1 e2) =
>   liftM2 Apply (renameExpr env e1) (renameExpr env e2)
> renameExpr env (InfixApply e1 op e2) =
>   liftM3 InfixApply (renameExpr env e1) (renameOp env op) (renameExpr env e2)
> renameExpr env (LeftSection e op) =
>   liftM2 LeftSection (renameExpr env e) (renameOp env op)
> renameExpr env (RightSection op e) =
>   liftM2 RightSection (renameOp env op) (renameExpr env e)
> renameExpr env (Lambda p ts e) =
>   do
>     env' <- bindVars env (bv ts)
>     liftM2 (Lambda p)
>            (mapM (renameConstrTerm env env') ts)
>            (renameExpr env' e)
> renameExpr env (Let ds e) =
>   do
>     env' <- bindVars env (bv ds)
>     liftM2 Let (mapM (renameDecl env') ds) (renameExpr env' e)
> renameExpr env (Do sts e) =
>   do
>     (env',sts') <- mapAccumM renameStmt env sts
>     e' <- renameExpr env' e
>     return (Do sts' e')
> renameExpr env (IfThenElse e1 e2 e3) =
>   liftM3 IfThenElse
>          (renameExpr env e1)
>          (renameExpr env e2)
>          (renameExpr env e3)
> renameExpr env (Case e as) =
>   liftM2 Case (renameExpr env e) (mapM (renameAlt env) as)
> renameExpr env (Fcase e as) =
>   liftM2 Fcase (renameExpr env e) (mapM (renameAlt env) as)

> renameOp :: RenameEnv -> InfixOp a -> RenameState (InfixOp a)
> renameOp env (InfixOp a op) = liftM (InfixOp a) (renameQual env op)
> renameOp _ (InfixConstr a op) = return (InfixConstr a op)

> renameStmt :: RenameEnv -> Statement a -> RenameState (RenameEnv,Statement a)
> renameStmt env (StmtExpr e) =
>   do
>     e' <- renameExpr env e
>     return (env,StmtExpr e')
> renameStmt env (StmtBind p t e) =
>   do
>     e' <- renameExpr env e
>     env' <- bindVars env (bv t)
>     t' <- renameConstrTerm env env' t
>     return (env',StmtBind p t' e')
> renameStmt env (StmtDecl ds) =
>   do
>     env' <- bindVars env (bv ds)
>     ds' <- mapM (renameDecl env') ds
>     return (env',StmtDecl ds')

> renameAlt :: RenameEnv -> Alt a -> RenameState (Alt a)
> renameAlt env (Alt p t rhs) =
>   do
>     env' <- bindVars env (bv t)
>     liftM2 (Alt p) (renameConstrTerm env env' t) (renameRhs env' rhs)

> renameField :: (a -> RenameState a) -> Field a -> RenameState (Field a)
> renameField rename (Field l x) = liftM (Field l) (rename x)

\end{verbatim}
