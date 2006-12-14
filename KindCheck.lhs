% -*- LaTeX -*-
% $Id: KindCheck.lhs 2045 2006-12-14 12:43:17Z wlux $
%
% Copyright (c) 1999-2006, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{KindCheck.lhs}
\section{Kind Checking}
Before type checking starts, the compiler applies kind checking to the
type expressions in the current module. Because Curry currently does
not support type classes, all types must be of first order kind
($\star$).  This makes kind checking in Curry rather trivial; the
compiler must only ensure that all type constructor applications are
saturated.
\begin{verbatim}

> module KindCheck(kindCheck,kindCheckGoal) where
> import Base
> import CurryPP
> import Error
> import Monad
> import Pretty
> import SCC
> import TopEnv
> import TypeTrans

\end{verbatim}
Before checking the type expressions of a module, the compiler adds
the types defined in the current module to the type constructor
environment and ensures that the module contains no (mutually)
recursive type synonyms, which are not allowed in Curry and could lead
to non-termination during their expansion.
\begin{verbatim}

> kindCheck :: ModuleIdent -> TCEnv -> [TopDecl a] -> Error TCEnv
> kindCheck m tcEnv ds =
>   do
>     checkSuperClasses m tds &&> checkSynonynms m tds
>     let tcEnv' = bindTypes m tds tcEnv
>     mapE_ (checkTopDecl tcEnv') ds
>     return tcEnv'
>   where tds = filter isTypeDecl ds

\end{verbatim}
Kind checking of a goal is simpler because there are no type
declarations.
\begin{verbatim}

> kindCheckGoal :: TCEnv -> Goal a -> Error ()
> kindCheckGoal tcEnv (Goal p e ds) =
>   checkExpr tcEnv p e &&> mapE_ (checkDecl tcEnv) ds

\end{verbatim}
When synonym types are entered into the type environment, their right
hand sides are already fully expanded. This is possible because Curry
does not allow (mutually) recursive type synonyms, which is checked in
function \texttt{checkSynonyms} below. In addition, the compiler
checks that the super class hierarchy is acyclic (in function
\texttt{checkSuperClasses}) and computes all direct and indirect super
classes of a type class when it is entered into the type environment.

Note that \texttt{bindTC} is passed the \emph{final} type constructor
environment so that we do not need to pass the declarations to this
function in any particular order.
\begin{verbatim}

> bindTypes :: ModuleIdent -> [TopDecl a] -> TCEnv -> TCEnv
> bindTypes m ds tcEnv = tcEnv'
>   where tcEnv' = foldr (bindTC m tcEnv') tcEnv ds

> bindTC :: ModuleIdent -> TCEnv -> TopDecl a -> TCEnv -> TCEnv
> bindTC m tcEnv (DataDecl _ _ tc tvs cs _) =
>   globalBindTopEnv m tc (typeCon DataType m tc tvs (map (Just . constr) cs))
> bindTC m tcEnv (NewtypeDecl _ _ tc tvs nc _) =
>   globalBindTopEnv m tc (typeCon RenamingType m tc tvs (nconstr nc))
> bindTC m tcEnv (TypeDecl _ tc tvs ty) =
>   globalBindTopEnv m tc
>                    (typeCon AliasType m tc tvs (expandMonoType tcEnv tvs ty))
> bindTC m tcEnv (ClassDecl _ cx cls tv ds) =
>   globalBindTopEnv m cls (typeClass m cls clss fs)
>   where clss = [cls | TypePred cls _ <- context ty]
>         fs = map Just (concatMap methods ds)
>         ty = expandPolyType tcEnv (QualTypeExpr cx (VariableType tv))
>         context (ForAll _ (QualType cx _)) = cx
> bindTC _ _ (InstanceDecl _ _ _ _ _) = id
> bindTC _ _ (BlockDecl _) = id

> checkSynonynms :: ModuleIdent -> [TopDecl a] -> Error ()
> checkSynonynms m = mapE_ (typeDecl m) . scc bound free
>   where bound (DataDecl _ _ tc _ _ _) = [tc]
>         bound (NewtypeDecl _ _ tc _ _ _) = [tc]
>         bound (TypeDecl _ tc _ _) = [tc]
>         bound (ClassDecl _ _ _ _ _) = []
>         bound (InstanceDecl _ _ _ _ _) = []
>         bound (BlockDecl _) = []
>         free (DataDecl _ _ _ _ _ _) = []
>         free (NewtypeDecl _ _ _ _ _ _) = []
>         free (TypeDecl _ _ _ ty) = ft m ty []
>         free (ClassDecl _ _ _ _ _) = []
>         free (InstanceDecl _ _ _ _ _) = []
>         free (BlockDecl _) = []

> typeDecl :: ModuleIdent -> [TopDecl a] -> Error ()
> typeDecl _ [] = internalError "typeDecl"
> typeDecl _ [DataDecl _ _ _ _ _ _] = return ()
> typeDecl _ [NewtypeDecl _ _ _ _ _ _] = return ()
> typeDecl m [TypeDecl p tc _ ty]
>   | tc `elem` ft m ty [] = errorAt p (recursiveTypes [tc])
>   | otherwise = return ()
> typeDecl _ (TypeDecl p tc _ _ : ds) =
>   errorAt p (recursiveTypes (tc : [tc' | TypeDecl _ tc' _ _ <- ds]))
> typeDecl _ [ClassDecl _ _ _ _ _] = return ()

> ft :: ModuleIdent -> TypeExpr -> [Ident] -> [Ident]
> ft m (ConstructorType tc tys) tcs =
>   maybe id (:) (localIdent m tc) (foldr (ft m) tcs tys)
> ft _ (VariableType _) tcs = tcs
> ft m (TupleType tys) tcs = foldr (ft m) tcs tys
> ft m (ListType ty) tcs = ft m ty tcs
> ft m (ArrowType ty1 ty2) tcs = ft m ty1 $ ft m ty2 $ tcs

> checkSuperClasses :: ModuleIdent -> [TopDecl a] -> Error ()
> checkSuperClasses m =
>   mapE_ (classDecl m) . scc bound free . filter isClassDecl
>   where bound (ClassDecl _ _ cls _ _) = [cls]
>         free (ClassDecl _ cx _ _ _) = fc m cx

> classDecl :: ModuleIdent -> [TopDecl a] -> Error ()
> classDecl _ [] = internalError "clasDecl"
> classDecl m [ClassDecl p cx cls _ _]
>   | cls `elem` fc m cx = errorAt p (recursiveClasses [cls])
>   | otherwise = return ()
> classDecl _ (ClassDecl p _ cls _ _ : ds) =
>   errorAt p (recursiveClasses (cls : [cls' | ClassDecl _ _ cls' _ _ <- ds]))
> classDecl _ [d] = return ()

> fc :: ModuleIdent -> [ClassAssert] -> [Ident]
> fc m cx =
>   foldr (\(ClassAssert cls _) -> maybe id (:) (localIdent m cls)) [] cx

\end{verbatim}
Kind checking is applied to all type expressions in the program.
\begin{verbatim}

> checkTopDecl :: TCEnv -> TopDecl a -> Error ()
> checkTopDecl tcEnv (DataDecl _ _ _ _ cs _) = mapE_ (checkConstrDecl tcEnv) cs
> checkTopDecl tcEnv (NewtypeDecl _ _ _ _ nc _) = checkNewConstrDecl tcEnv nc
> checkTopDecl tcEnv (TypeDecl p _ _ ty) = checkType tcEnv p ty
> checkTopDecl tcEnv (ClassDecl _ _ _ _ ds) = mapE_ (checkMethodDecl tcEnv) ds
> checkTopDecl tcEnv (InstanceDecl p _ _ ty ds) =
>   checkType tcEnv p ty &&> mapE_ (checkMethodDecl tcEnv) ds
> checkTopDecl tcEnv (BlockDecl d) = checkDecl tcEnv d

> checkMethodDecl :: TCEnv -> MethodDecl a -> Error ()
> checkMethodDecl tcEnv (MethodSig p _ ty) = checkType tcEnv p ty
> checkMethodDecl tcEnv (MethodDecl _ _ eqs) = mapE_ (checkEquation tcEnv) eqs

> checkDecl :: TCEnv -> Decl a -> Error ()
> checkDecl tcEnv (TypeSig p _ ty) = checkQualType tcEnv p ty
> checkDecl tcEnv (FunctionDecl _ _ eqs) = mapE_ (checkEquation tcEnv) eqs
> checkDecl tcEnv (PatternDecl _ _ rhs) = checkRhs tcEnv rhs
> checkDecl tcEnv (ForeignDecl p _ _ _ ty) = checkType tcEnv p ty
> checkDecl _ d = return ()

> checkConstrDecl :: TCEnv -> ConstrDecl -> Error ()
> checkConstrDecl tcEnv (ConstrDecl p _ _ tys) = mapE_ (checkType tcEnv p) tys
> checkConstrDecl tcEnv (ConOpDecl p _ ty1 _ ty2) =
>   checkType tcEnv p ty1 &&> checkType tcEnv p ty2

> checkNewConstrDecl :: TCEnv -> NewConstrDecl -> Error ()
> checkNewConstrDecl tcEnv (NewConstrDecl p _ ty) = checkType tcEnv p ty

> checkEquation :: TCEnv -> Equation a -> Error ()
> checkEquation tcEnv (Equation _ _ rhs) = checkRhs tcEnv rhs

> checkRhs :: TCEnv -> Rhs a -> Error ()
> checkRhs tcEnv (SimpleRhs p e ds) =
>   checkExpr tcEnv p e &&> mapE_ (checkDecl tcEnv) ds
> checkRhs tcEnv (GuardedRhs es ds) =
>   mapE_ (checkCondExpr tcEnv) es &&> mapE_ (checkDecl tcEnv) ds

> checkCondExpr :: TCEnv -> CondExpr a -> Error ()
> checkCondExpr tcEnv (CondExpr p g e) =
>   checkExpr tcEnv p g &&> checkExpr tcEnv p e

> checkExpr :: TCEnv -> Position -> Expression a -> Error ()
> checkExpr _ _ (Literal _ _) = return ()
> checkExpr _ _ (Variable _ _) = return ()
> checkExpr _ _ (Constructor _ _) = return ()
> checkExpr tcEnv p (Paren e) = checkExpr tcEnv p e
> checkExpr tcEnv p (Typed e ty) =
>   checkExpr tcEnv p e &&> checkQualType tcEnv p ty
> checkExpr tcEnv p (Tuple es) = mapE_ (checkExpr tcEnv p) es
> checkExpr tcEnv p (List _ es) = mapE_ (checkExpr tcEnv p) es
> checkExpr tcEnv p (ListCompr e qs) =
>   checkExpr tcEnv p e &&> mapE_ (checkStmt tcEnv p) qs
> checkExpr tcEnv p (EnumFrom e) = checkExpr tcEnv p e
> checkExpr tcEnv p (EnumFromThen e1 e2) =
>   checkExpr tcEnv p e1 &&> checkExpr tcEnv p e2
> checkExpr tcEnv p (EnumFromTo e1 e2) =
>   checkExpr tcEnv p e1 &&> checkExpr tcEnv p e2
> checkExpr tcEnv p (EnumFromThenTo e1 e2 e3) =
>   checkExpr tcEnv p e1 &&> checkExpr tcEnv p e2 &&> checkExpr tcEnv p e3
> checkExpr tcEnv p (UnaryMinus e) = checkExpr tcEnv p e
> checkExpr tcEnv p (Apply e1 e2) =
>   checkExpr tcEnv p e1 &&> checkExpr tcEnv p e2
> checkExpr tcEnv p (InfixApply e1 _ e2) =
>   checkExpr tcEnv p e1 &&> checkExpr tcEnv p e2
> checkExpr tcEnv p (LeftSection e _) = checkExpr tcEnv p e
> checkExpr tcEnv p (RightSection _ e) = checkExpr tcEnv p e
> checkExpr tcEnv p (Lambda _ e) = checkExpr tcEnv p e
> checkExpr tcEnv p (Let ds e) =
>   mapE_ (checkDecl tcEnv) ds &&> checkExpr tcEnv p e
> checkExpr tcEnv p (Do sts e) =
>   mapE_ (checkStmt tcEnv p) sts &&> checkExpr tcEnv p e
> checkExpr tcEnv p (IfThenElse e1 e2 e3) =
>   checkExpr tcEnv p e1 &&> checkExpr tcEnv p e2 &&> checkExpr tcEnv p e3
> checkExpr tcEnv p (Case e alts) =
>   checkExpr tcEnv p e &&> mapE_ (checkAlt tcEnv) alts

> checkStmt :: TCEnv -> Position -> Statement a -> Error ()
> checkStmt tcEnv p (StmtExpr e) = checkExpr tcEnv p e
> checkStmt tcEnv p (StmtBind _ e) = checkExpr tcEnv p e
> checkStmt tcEnv _ (StmtDecl ds) = mapE_ (checkDecl tcEnv) ds

> checkAlt :: TCEnv -> Alt a -> Error ()
> checkAlt tcEnv (Alt _ _ rhs) = checkRhs tcEnv rhs

> checkQualType :: TCEnv -> Position -> QualTypeExpr -> Error ()
> checkQualType tcEnv p (QualTypeExpr _ ty) = checkType tcEnv p ty

> checkType :: TCEnv -> Position -> TypeExpr -> Error ()
> checkType tcEnv p (ConstructorType tc tys) =
>   unless (n == n') (errorAt p (wrongArity tc n n')) &&>
>   mapE_ (checkType tcEnv p) tys
>   where n = constrKind tc tcEnv
>         n' = length tys
> checkType _ _ (VariableType _) = return ()
> checkType tcEnv p (TupleType tys) = mapE_ (checkType tcEnv p) tys
> checkType tcEnv p (ListType ty) = checkType tcEnv p ty
> checkType tcEnv p (ArrowType ty1 ty2) =
>   checkType tcEnv p ty1 &&> checkType tcEnv p ty2

\end{verbatim}
Auxiliary functions.
\begin{verbatim}

> typeCon :: (QualIdent -> Int -> a) -> ModuleIdent -> Ident -> [Ident] -> a
> typeCon f m tc tvs = f (qualifyWith m tc) (length tvs)

> typeClass :: ModuleIdent -> Ident -> [QualIdent] -> [Maybe Ident] -> TypeInfo
> typeClass m cls = TypeClass (qualifyWith m cls)

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

> wrongArity :: QualIdent -> Int -> Int -> String
> wrongArity tc arity argc = show $
>   hsep [text "Type constructor", ppQIdent tc, text "requires",
>         int arity, text (plural arity "argument") <> comma,
>         text "but is applied to", int argc]
>   where plural n x = if n == 1 then x else x ++ "s"

\end{verbatim}
