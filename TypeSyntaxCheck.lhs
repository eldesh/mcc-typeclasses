% -*- LaTeX -*-
% $Id: TypeSyntaxCheck.lhs 1912 2006-05-03 14:53:33Z wlux $
%
% Copyright (c) 1999-2006, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{TypeSyntaxCheck.lhs}
\section{Checking Type Definitions}
After the source file has been parsed and all modules have been
imported, the compiler first checks all type definitions and
signatures. In particular, this module disambiguates nullary
constructors and type variables, which -- in contrast to many other
declarative languages -- cannot be done in the parser due to the lack
of a capitalization convention.
\begin{verbatim}

> module TypeSyntaxCheck(typeSyntaxCheck,typeSyntaxCheckGoal) where
> import Base
> import CurryPP
> import Error
> import List
> import Pretty
> import TopEnv

\end{verbatim}
In order to check type constructor applications, the compiler
maintains an environment, which records all known type constructors.
The function \texttt{typeSyntaxCheck} first initializes this
environment from the imported type constructor environment. Next, the
all locally defined type constructors are inserted into the
environment, and, finally, the declarations are checked within this
environment. The final environment is returned in order to be used
later for checking the optional export list of the current module.
\begin{verbatim}

> typeSyntaxCheck :: ModuleIdent -> TCEnv -> [TopDecl]
>                 -> Error (TypeEnv,[TopDecl])
> typeSyntaxCheck m tcEnv ds =
>   do
>     reportDuplicates duplicateType repeatedType (map tconstr tds)
>     ds' <- mapE (checkTopDecl env) ds
>     return (env,ds')
>   where tds = filter isTypeDecl ds
>         env = foldr (bindType m) (fmap typeKind tcEnv) tds

> typeSyntaxCheckGoal :: TCEnv -> Goal -> Error Goal
> typeSyntaxCheckGoal tcEnv (Goal p e ds) =
>   liftE2 (Goal p) (checkExpr env p e) (mapE (checkDecl env) ds)
>   where env = fmap typeKind tcEnv

> bindType :: ModuleIdent -> TopDecl -> TypeEnv -> TypeEnv
> bindType m (DataDecl _ tc _ cs) =
>   globalBindTopEnv m tc (Data (qualifyWith m tc) (map constr cs))
> bindType m (NewtypeDecl _ tc _ nc) =
>   globalBindTopEnv m tc (Data (qualifyWith m tc) [nconstr nc])
> bindType m (TypeDecl _ tc _ _) =
>   globalBindTopEnv m tc (Alias (qualifyWith m tc))
> bindType _ (BlockDecl _) = id

\end{verbatim}
The compiler allows anonymous type variables on the left hand side of
type declarations, but not on their right hand side. Function and
pattern declarations are traversed in order to check local type
signatures.
\begin{verbatim}

> checkTopDecl :: TypeEnv -> TopDecl -> Error TopDecl
> checkTopDecl env (DataDecl p tc tvs cs) =
>   checkTypeLhs env p tvs &&>
>   liftE (DataDecl p tc tvs) (mapE (checkConstrDecl env tvs) cs)
> checkTopDecl env (NewtypeDecl p tc tvs nc) =
>   checkTypeLhs env p tvs &&>
>   liftE (NewtypeDecl p tc tvs) (checkNewConstrDecl env tvs nc)
> checkTopDecl env (TypeDecl p tc tvs ty) =
>   checkTypeLhs env p tvs &&>
>   liftE (TypeDecl p tc tvs) (checkClosedType env p tvs ty)
> checkTopDecl env (BlockDecl d) = liftE BlockDecl (checkDecl env d)

> checkDecl :: TypeEnv -> Decl -> Error Decl
> checkDecl env (TypeSig p vs ty) =
>   liftE (TypeSig p vs) (checkType env p ty)
> checkDecl env (FunctionDecl p f eqs) =
>   liftE (FunctionDecl p f) (mapE (checkEquation env) eqs)
> checkDecl env (PatternDecl p t rhs) =
>   liftE (PatternDecl p t) (checkRhs env rhs)
> checkDecl env (ForeignDecl p cc ie f ty) =
>   liftE (ForeignDecl p cc ie f) (checkType env p ty)
> checkDecl _ d = return d

> checkTypeLhs :: TypeEnv -> Position -> [Ident] -> Error ()
> checkTypeLhs env p tvs =
>   mapE_ (errorAt p . noVariable) (nub tcs) &&>
>   mapE_ (errorAt p . nonLinear . fst) (duplicates (filter (anonId /=) tvs'))
>   where (tcs,tvs') = partition isTypeConstr tvs
>         isTypeConstr tv = not (null (lookupTopEnv tv env))

> checkConstrDecl :: TypeEnv -> [Ident] -> ConstrDecl -> Error ConstrDecl
> checkConstrDecl env tvs (ConstrDecl p evs c tys) =
>   checkTypeLhs env p evs &&>
>   liftE (ConstrDecl p evs c) (mapE (checkClosedType env p tvs') tys)
>   where tvs' = evs ++ tvs
> checkConstrDecl env tvs (ConOpDecl p evs ty1 op ty2) =
>   checkTypeLhs env p evs &&>
>   liftE2 (flip (ConOpDecl p evs) op)
>          (checkClosedType env p tvs' ty1)
>          (checkClosedType env p tvs' ty2)
>   where tvs' = evs ++ tvs

> checkNewConstrDecl :: TypeEnv -> [Ident] -> NewConstrDecl
>                    -> Error NewConstrDecl
> checkNewConstrDecl env tvs (NewConstrDecl p c ty) =
>   liftE (NewConstrDecl p c) (checkClosedType env p tvs ty)

\end{verbatim}
Checking expressions is rather straight forward. The compiler must
only traverse the structure of expressions in order to find local
declaration groups.
\begin{verbatim}

> checkEquation :: TypeEnv -> Equation -> Error Equation
> checkEquation env (Equation p lhs rhs) =
>   liftE (Equation p lhs) (checkRhs env rhs)

> checkRhs :: TypeEnv -> Rhs -> Error Rhs
> checkRhs env (SimpleRhs p e ds) =
>   liftE2 (SimpleRhs p) (checkExpr env p e) (mapE (checkDecl env) ds)
> checkRhs env (GuardedRhs es ds) =
>   liftE2 GuardedRhs (mapE (checkCondExpr env) es) (mapE (checkDecl env) ds)

> checkCondExpr :: TypeEnv -> CondExpr -> Error CondExpr
> checkCondExpr env (CondExpr p g e) =
>   liftE2 (CondExpr p) (checkExpr env p g) (checkExpr env p e)

> checkExpr :: TypeEnv -> Position -> Expression -> Error Expression
> checkExpr _ _ (Literal l) = return (Literal l)
> checkExpr _ _ (Variable v) = return (Variable v)
> checkExpr _ _ (Constructor c) = return (Constructor c)
> checkExpr env p (Paren e) = liftE Paren (checkExpr env p e)
> checkExpr env p (Typed e ty) =
>   liftE2 Typed (checkExpr env p e) (checkType env p ty)
> checkExpr env p (Tuple es) = liftE Tuple (mapE (checkExpr env p) es)
> checkExpr env p (List es) = liftE List (mapE (checkExpr env p) es)
> checkExpr env p (ListCompr e qs) =
>   liftE2 ListCompr (checkExpr env p e) (mapE (checkStmt env p) qs)
> checkExpr env p (EnumFrom e) = liftE EnumFrom (checkExpr env p e)
> checkExpr env p (EnumFromThen e1 e2) =
>   liftE2 EnumFromThen (checkExpr env p e1) (checkExpr env p e2)
> checkExpr env p (EnumFromTo e1 e2) =
>   liftE2 EnumFromTo (checkExpr env p e1) (checkExpr env p e2)
> checkExpr env p (EnumFromThenTo e1 e2 e3) =
>   liftE3 EnumFromThenTo
>          (checkExpr env p e1)
>          (checkExpr env p e2)
>          (checkExpr env p e3)
> checkExpr env p (UnaryMinus op e) = liftE (UnaryMinus op) (checkExpr env p e)
> checkExpr env p (Apply e1 e2) =
>   liftE2 Apply (checkExpr env p e1) (checkExpr env p e2)
> checkExpr env p (InfixApply e1 op e2) =
>   liftE2 (flip InfixApply op) (checkExpr env p e1) (checkExpr env p e2)
> checkExpr env p (LeftSection e op) =
>   liftE (flip LeftSection op) (checkExpr env p e)
> checkExpr env p (RightSection op e) =
>   liftE (RightSection op) (checkExpr env p e)
> checkExpr env p (Lambda ts e) = liftE (Lambda ts) (checkExpr env p e)
> checkExpr env p (Let ds e) =
>   liftE2 Let (mapE (checkDecl env) ds) (checkExpr env p e)
> checkExpr env p (Do sts e) =
>   liftE2 Do (mapE (checkStmt env p) sts) (checkExpr env p e)
> checkExpr env p (IfThenElse e1 e2 e3) =
>   liftE3 IfThenElse
>          (checkExpr env p e1)
>          (checkExpr env p e2)
>          (checkExpr env p e3)
> checkExpr env p (Case e alts) =
>   liftE2 Case (checkExpr env p e) (mapE (checkAlt env) alts)

> checkStmt :: TypeEnv -> Position -> Statement -> Error Statement
> checkStmt env p (StmtExpr e) = liftE StmtExpr (checkExpr env p e)
> checkStmt env p (StmtBind t e) = liftE (StmtBind t) (checkExpr env p e)
> checkStmt env p (StmtDecl ds) = liftE StmtDecl (mapE (checkDecl env) ds)

> checkAlt :: TypeEnv -> Alt -> Error Alt
> checkAlt env (Alt p t rhs) = liftE (Alt p t) (checkRhs env rhs)

\end{verbatim}
The parser cannot distinguish unqualified nullary type constructors
and type variables. Therefore, if the compiler finds an unbound
identifier in a position where a type variable is admissible, it will
interpret the identifier as such.
\begin{verbatim}

> checkClosedType :: TypeEnv -> Position -> [Ident] -> TypeExpr
>                 -> Error TypeExpr
> checkClosedType env p tvs ty =
>   do
>     ty' <- checkType env p ty
>     mapE_ (errorAt p . unboundVariable)
>           (nub (filter (\tv -> tv == anonId || tv `notElem` tvs) (fv ty')))
>     return ty'

> checkType :: TypeEnv -> Position -> TypeExpr -> Error TypeExpr
> checkType env p (ConstructorType tc tys) =
>   liftE2 ($)
>          (case qualLookupTopEnv tc env of
>             []
>               | not (isQualified tc) && null tys ->
>                   return (const (VariableType (unqualify tc)))
>               | otherwise -> errorAt p (undefinedType tc)
>             [_] -> return (ConstructorType tc)
>             rs -> errorAt p (ambiguousType rs tc))
>          (mapE (checkType env p) tys)
> checkType env p (VariableType tv)
>   | tv == anonId = return (VariableType tv)
>   | otherwise = checkType env p (ConstructorType (qualify tv) [])
> checkType env p (TupleType tys) =
>   liftE TupleType (mapE (checkType env p) tys)
> checkType env p (ListType ty) =
>   liftE ListType (checkType env p ty)
> checkType env p (ArrowType ty1 ty2) =
>   liftE2 ArrowType (checkType env p ty1) (checkType env p ty2)

\end{verbatim}
Auxiliary definitions.
\begin{verbatim}

> tconstr :: TopDecl -> P Ident
> tconstr (DataDecl p tc _ _) = P p tc
> tconstr (NewtypeDecl p tc _ _) = P p tc
> tconstr (TypeDecl p tc _ _) = P p tc
> tconstr (BlockDecl _) = internalError "tconstr"

\end{verbatim}
Error messages.
\begin{verbatim}

> reportDuplicates :: Eq a => (a -> String) -> (a -> String) -> [P a]
>                  -> Error ()
> reportDuplicates f1 f2 xs =
>   mapE_ (\(x,xs) -> zipWithE_ report (f1 : repeat f2) (x:xs)) (duplicates xs)
>   where report f (P p x) = errorAt p (f x)

> undefinedType :: QualIdent -> String
> undefinedType tc = "Undefined type " ++ qualName tc

> ambiguousType :: [TypeKind] -> QualIdent -> String
> ambiguousType rs tc = show $
>   text "Ambiguous type" <+> ppQIdent tc $$
>   fsep (text "Could refer to:" :
>               punctuate comma (map (ppQIdent . origName) rs))

> duplicateType :: Ident -> String
> duplicateType tc = "Type " ++ name tc ++ " defined more than once"

> repeatedType :: Ident -> String
> repeatedType tc = "Redefinition of type " ++ name tc

> nonLinear :: Ident -> String
> nonLinear tv =
>   "Type variable " ++ name tv ++
>   " occurs more than once in left hand side of type declaration"

> noVariable :: Ident -> String
> noVariable tv =
>   "Type constructor " ++ name tv ++
>   " used in left hand side of type declaration"

> unboundVariable :: Ident -> String
> unboundVariable tv = "Undefined type variable " ++ name tv

\end{verbatim}
