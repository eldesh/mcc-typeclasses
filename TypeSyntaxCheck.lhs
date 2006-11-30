% -*- LaTeX -*-
% $Id: TypeSyntaxCheck.lhs 2031 2006-11-30 10:06:13Z wlux $
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
> import Monad
> import Pretty
> import Set
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

> typeSyntaxCheck :: ModuleIdent -> TCEnv -> InstEnv -> [TopDecl a]
>                 -> Error (TypeEnv,[TopDecl a])
> typeSyntaxCheck m tcEnv iEnv ds =
>   do
>     reportDuplicates duplicateType repeatedType (map tident tds)
>     ds' <- mapE (checkTopDecl env) ds
>     checkInstances env (instSet iEnv) ds'
>     return (env,ds')
>   where tds = filter isTypeDecl ds
>         env = foldr (bindType m) (fmap typeKind tcEnv) tds

> typeSyntaxCheckGoal :: TCEnv -> Goal a -> Error (Goal a)
> typeSyntaxCheckGoal tcEnv (Goal p e ds) =
>   liftE2 (Goal p) (checkExpr env p e) (mapE (checkDecl env) ds)
>   where env = fmap typeKind tcEnv

> bindType :: ModuleIdent -> TopDecl a -> TypeEnv -> TypeEnv
> bindType m (DataDecl _ _ tc _ cs) =
>   globalBindTopEnv m tc (Data (qualifyWith m tc) (map constr cs))
> bindType m (NewtypeDecl _ _ tc _ nc) =
>   globalBindTopEnv m tc (Data (qualifyWith m tc) [nconstr nc])
> bindType m (TypeDecl _ tc _ _) =
>   globalBindTopEnv m tc (Alias (qualifyWith m tc))
> bindType m (ClassDecl _ _ cls _ ds) =
>   globalBindTopEnv m cls (Class (qualifyWith m cls) (concatMap methods ds))
> bindType m (InstanceDecl _ _ _ _ _) = id
> bindType _ (BlockDecl _) = id

\end{verbatim}
The compiler allows anonymous type variables on the left hand side of
type declarations, but not on their right hand side. Function and
pattern declarations are traversed in order to check local type
signatures.
\begin{verbatim}

> checkTopDecl :: TypeEnv -> TopDecl a -> Error (TopDecl a)
> checkTopDecl env (DataDecl p cx tc tvs cs) =
>   checkTypeLhs env p cx tvs &&>
>   liftE (DataDecl p cx tc tvs) (mapE (checkConstrDecl env tvs) cs)
> checkTopDecl env (NewtypeDecl p cx tc tvs nc) =
>   checkTypeLhs env p cx tvs &&>
>   liftE (NewtypeDecl p cx tc tvs) (checkNewConstrDecl env tvs nc)
> checkTopDecl env (TypeDecl p tc tvs ty) =
>   checkTypeLhs env p [] tvs &&>
>   liftE (TypeDecl p tc tvs) (checkClosedType env p tvs ty)
> checkTopDecl env (ClassDecl p cx cls tv ds) =
>   checkTypeLhs env p cx [tv] &&>
>   liftE (ClassDecl p cx cls tv) (mapE (checkMethodSig env tv) ds)
> checkTopDecl env (InstanceDecl p cx cls ty ds) =
>   checkClass env p cls &&>
>   liftE2 (InstanceDecl p cx cls)
>          (checkInstType env p cx ty)
>          (mapE (checkMethodDecl env) ds)
> checkTopDecl env (BlockDecl d) = liftE BlockDecl (checkDecl env d)

> checkMethodSig :: TypeEnv -> Ident -> MethodSig a -> Error (MethodSig a)
> checkMethodSig env tv (MethodSig p fs ty) =
>   do
>     ty' <- checkType env p ty
>     let tvs = fv ty'
>     unless (tv `elem` tvs) (errorAt p (ambiguousType tv)) &&>
>       mapE_ (errorAt p . polymorphicMethod) (nub (filter (tv /=) tvs))
>     return (MethodSig p fs ty')
> checkMethodSig env _ (DefaultMethodDecl p f eqs) =
>   liftE (DefaultMethodDecl p f) (mapE (checkEquation env) eqs)

> checkMethodDecl :: TypeEnv -> MethodDecl a -> Error (MethodDecl a)
> checkMethodDecl env (MethodDecl p f eqs) =
>   liftE (MethodDecl p f) (mapE (checkEquation env) eqs)

> checkDecl :: TypeEnv -> Decl a -> Error (Decl a)
> checkDecl env (TypeSig p vs ty) =
>   liftE (TypeSig p vs) (checkQualType env p ty)
> checkDecl env (FunctionDecl p f eqs) =
>   liftE (FunctionDecl p f) (mapE (checkEquation env) eqs)
> checkDecl env (PatternDecl p t rhs) =
>   liftE (PatternDecl p t) (checkRhs env rhs)
> checkDecl env (ForeignDecl p cc ie f ty) =
>   liftE (ForeignDecl p cc ie f) (checkType env p ty)
> checkDecl _ d = return d

> checkTypeLhs :: TypeEnv -> Position -> [ClassAssert] -> [Ident] -> Error ()
> checkTypeLhs env p cx tvs =
>   do
>     mapE_ (errorAt p . noVariable "left hand side of type declaration")
>           (nub tcs) &&>
>       mapE_ (checkClassAssert env p) cx &&>
>       mapE_ (errorAt p . nonLinear "left hand side of type declaration". fst)
>             (duplicates (filter (anonId /=) tvs'))
>     checkClosedContext p cx tvs
>   where (tcs,tvs') = partition isTypeConstr tvs
>         isTypeConstr tv = not (null (lookupTopEnv tv env))

> checkConstrDecl :: TypeEnv -> [Ident] -> ConstrDecl -> Error ConstrDecl
> checkConstrDecl env tvs (ConstrDecl p evs c tys) =
>   checkTypeLhs env p [] evs &&>
>   liftE (ConstrDecl p evs c) (mapE (checkClosedType env p tvs') tys)
>   where tvs' = evs ++ tvs
> checkConstrDecl env tvs (ConOpDecl p evs ty1 op ty2) =
>   checkTypeLhs env p [] evs &&>
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

> checkEquation :: TypeEnv -> Equation a -> Error (Equation a)
> checkEquation env (Equation p lhs rhs) =
>   liftE (Equation p lhs) (checkRhs env rhs)

> checkRhs :: TypeEnv -> Rhs a -> Error (Rhs a)
> checkRhs env (SimpleRhs p e ds) =
>   liftE2 (SimpleRhs p) (checkExpr env p e) (mapE (checkDecl env) ds)
> checkRhs env (GuardedRhs es ds) =
>   liftE2 GuardedRhs (mapE (checkCondExpr env) es) (mapE (checkDecl env) ds)

> checkCondExpr :: TypeEnv -> CondExpr a -> Error (CondExpr a)
> checkCondExpr env (CondExpr p g e) =
>   liftE2 (CondExpr p) (checkExpr env p g) (checkExpr env p e)

> checkExpr :: TypeEnv -> Position -> Expression a -> Error (Expression a)
> checkExpr _ _ (Literal a l) = return (Literal a l)
> checkExpr _ _ (Variable a v) = return (Variable a v)
> checkExpr _ _ (Constructor a c) = return (Constructor a c)
> checkExpr env p (Paren e) = liftE Paren (checkExpr env p e)
> checkExpr env p (Typed e ty) =
>   liftE2 Typed (checkExpr env p e) (checkQualType env p ty)
> checkExpr env p (Tuple es) = liftE Tuple (mapE (checkExpr env p) es)
> checkExpr env p (List a es) = liftE (List a) (mapE (checkExpr env p) es)
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
> checkExpr env p (UnaryMinus e) = liftE UnaryMinus (checkExpr env p e)
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

> checkStmt :: TypeEnv -> Position -> Statement a -> Error (Statement a)
> checkStmt env p (StmtExpr e) = liftE StmtExpr (checkExpr env p e)
> checkStmt env p (StmtBind t e) = liftE (StmtBind t) (checkExpr env p e)
> checkStmt env p (StmtDecl ds) = liftE StmtDecl (mapE (checkDecl env) ds)

> checkAlt :: TypeEnv -> Alt a -> Error (Alt a)
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

> checkInstType :: TypeEnv -> Position -> [ClassAssert] -> TypeExpr
>               -> Error TypeExpr
> checkInstType env p cx ty =
>   do
>     QualTypeExpr _ ty' <- checkQualType env p (QualTypeExpr cx ty)
>     unless (isSimpleType ty' && not (isTypeSynonym env (root ty')) &&
>             null (duplicates (filter (anonId /=) (fv ty'))))
>            (errorAt p (notSimpleType ty'))
>     return ty'

> checkQualType :: TypeEnv -> Position -> QualTypeExpr -> Error QualTypeExpr
> checkQualType env p (QualTypeExpr cx ty) =
>   do
>     ty' <- mapE_ (checkClassAssert env p) cx &&> checkType env p ty
>     checkClosedContext p cx (fv ty')
>     return (QualTypeExpr cx ty')

> checkClassAssert :: TypeEnv -> Position -> ClassAssert -> Error ()
> checkClassAssert env p (ClassAssert cls tv) =
>   checkClass env p cls &&>
>   unless (null (lookupTopEnv tv env))
>          (errorAt p (noVariable "class assertion" tv))

> checkClosedContext :: Position -> [ClassAssert] -> [Ident] -> Error ()
> checkClosedContext p cx tvs =
>   mapE_ (errorAt p . unboundVariable)
>         (nub [tv | ClassAssert _ tv <- cx, tv `notElem` tvs])

> checkType :: TypeEnv -> Position -> TypeExpr -> Error TypeExpr
> checkType env p (ConstructorType tc tys) =
>   liftE2 ($)
>          (case qualLookupTopEnv tc env of
>             []
>               | not (isQualified tc) && null tys ->
>                   return (const (VariableType (unqualify tc)))
>               | otherwise -> errorAt p (undefinedType tc)
>             [Data _ _] -> return (ConstructorType tc)
>             [Alias _] -> return (ConstructorType tc)
>             [Class _ _] -> errorAt p (undefinedType tc)
>             rs -> errorAt p (ambiguousIdent rs tc))
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

> checkClass :: TypeEnv -> Position -> QualIdent -> Error ()
> checkClass env p cls =
>   case qualLookupTopEnv cls env of
>     [] -> errorAt p (undefinedClass cls)
>     [Data _ _] -> errorAt p (undefinedClass cls)
>     [Alias _] -> errorAt p (undefinedClass cls)
>     [Class _ _] -> return ()
>     rs -> errorAt p (ambiguousIdent rs cls)

\end{verbatim}
The compiler reports an error when more than once instance is defined
for a particular pair of a type class and type constructor. This
includes duplicate instances defined in the current module as well as
conflicts between locally defined instances and imported instances.
\begin{verbatim}

> checkInstances :: TypeEnv -> InstSet -> [TopDecl a] -> Error ()
> checkInstances tEnv iEnv ds =
>   do
>     sequenceE_ [errorAt p (duplicateInstance inst) | P p inst <- unique cts,
>                                                      inst `elemSet` iEnv] &&>
>       reportDuplicates duplicateInstance repeatedInstance cts
>     return ()
>   where cts = [P p (qualCT tEnv (CT cls (root ty)))
>               | InstanceDecl p _ cls ty _ <- ds]
>         unique [] = []
>         unique (x:xs)
>           | x `elem` xs = unique (filter (x /=) xs)
>           | otherwise = x : unique xs

> bindInstance :: P CT -> InstSet -> InstSet
> bindInstance (P _ inst) iEnv = addToSet inst iEnv

> qualCT :: TypeEnv -> CT -> CT
> qualCT env (CT cls tc) = CT (qual env cls) (qual env tc)
>   where qual env x =
>           case qualLookupTopEnv x env of
>             [y] -> origName y
>             _ -> internalError "qualCT"

\end{verbatim}
Auxiliary definitions.
\begin{verbatim}

> tident :: TopDecl a -> P Ident
> tident (DataDecl p _ tc _ _) = P p tc
> tident (NewtypeDecl p _ tc _ _) = P p tc
> tident (TypeDecl p tc _ _) = P p tc
> tident (ClassDecl p _ cls _ _) = P p cls
> tident (InstanceDecl _ _ _ _ _) = internalError "tident"
> tident (BlockDecl _) = internalError "tident"

> isSimpleType :: TypeExpr -> Bool
> isSimpleType (ConstructorType _ tys) = all isVariableType tys
> isSimpleType (VariableType _) = False
> isSimpleType (TupleType tys) = all isVariableType tys
> isSimpleType (ListType ty) = isVariableType ty
> isSimpleType (ArrowType ty1 ty2) = isVariableType ty1 && isVariableType ty2

> isTypeSynonym :: TypeEnv -> QualIdent -> Bool
> isTypeSynonym env tc =
>   case qualLookupTopEnv tc env of
>     [Data _ _] -> False
>     [Alias _] -> True
>     _ -> internalError "isTypeSynonym"

> isVariableType :: TypeExpr -> Bool
> isVariableType (ConstructorType _ _) = False
> isVariableType (VariableType _) = True
> isVariableType (TupleType _) = False
> isVariableType (ListType _) = False
> isVariableType (ArrowType _ _) = False

> root :: TypeExpr -> QualIdent
> root (ConstructorType tc _) = tc
> root (VariableType _) = internalError "root"
> root (TupleType tys) = qTupleId (length tys)
> root (ListType _) = qListId
> root (ArrowType _ _) = qArrowId

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

> undefinedClass :: QualIdent -> String
> undefinedClass cls = "Undefined type class " ++ qualName cls

> ambiguousIdent :: [TypeKind] -> QualIdent -> String
> ambiguousIdent rs x = show $
>   text "Ambiguous identifier" <+> ppQIdent x $$
>   fsep (text "Could refer to:" :
>               punctuate comma (map (ppQIdent . origName) rs))

> duplicateType :: Ident -> String
> duplicateType x = name x ++ " defined more than once"

> repeatedType :: Ident -> String
> repeatedType x = "Redefinition of " ++ name x

> duplicateInstance :: CT -> String
> duplicateInstance (CT cls tc) =
>   "More than one " ++ qualName cls ++ " " ++ qualName tc ++
>   " instance declaration"

> repeatedInstance :: CT -> String
> repeatedInstance (CT cls tc) =
>   "Repeated " ++ qualName cls ++ " " ++ qualName tc ++ " instance declaration"

> nonLinear :: String -> Ident -> String
> nonLinear what tv =
>   "Type variable " ++ name tv ++ " occurs more than once in " ++ what

> noVariable :: String -> Ident -> String
> noVariable what tv =
>   "Type constructor or type class " ++ name tv ++ " used in " ++ what

> unboundVariable :: Ident -> String
> unboundVariable tv = "Undefined type variable " ++ name tv

> ambiguousType :: Ident -> String
> ambiguousType tv =
>   "Method type does not mention type variable " ++ name tv

> polymorphicMethod :: Ident -> String
> polymorphicMethod tv =
>   "Free type variable " ++ name tv ++ " in method type\n" ++
>   "(Implementation restriction: Polymorphic methods are not yet supported)"

> notSimpleType :: TypeExpr -> String
> notSimpleType ty = show $
>   vcat [text "Illegal instance type" <+> ppTypeExpr 0 ty,
>         text "The instance type must be of the form (T a b c), where T is",
>         text "not a type synonym and a, b, c are distinct type variables."]

\end{verbatim}
