% -*- LaTeX -*-
% $Id: TypeSyntaxCheck.lhs 2967 2010-06-18 16:27:02Z wlux $
%
% Copyright (c) 1999-2009, Wolfgang Lux
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
> import Curry
> import CurryPP
> import CurryUtils
> import Error
> import IdentInfo
> import List
> import Monad
> import Position
> import Pretty
> import Set
> import TopEnv

\end{verbatim}
In order to check type constructor applications, the compiler
maintains an environment that records all known type constructors and
type classes. The functions \texttt{typeSyntaxCheck} and
\texttt{typeSyntaxCheckGoal} expect a type identifier environment that
is already initialized with the imported type constructors and
classes. All locally defined type constructors and classes are added
to this environment and then the declarations are checked within this
environment. The environment is returned in order to be used later for
checking the optional export list of the current module.
\begin{verbatim}

> typeSyntaxCheck :: ModuleIdent -> TypeEnv -> InstSet -> [TopDecl a]
>                 -> Error (TypeEnv,[TopDecl a])
> typeSyntaxCheck m env iEnv ds =
>   do
>     reportDuplicates (const duplicateDefault) (const repeatedDefault)
>                      [P p () | DefaultDecl p _ <- ods] &&>
>       reportDuplicates duplicateType repeatedType (map tident tds)
>     ds' <- mapE (checkTopDecl env') ds
>     checkInstances env' iEnv ds'
>     return (env',ds')
>   where (tds,ods) = partition isTypeDecl ds
>         env' = foldr (bindType m) env tds

> typeSyntaxCheckGoal :: TypeEnv -> Goal a -> Error (Goal a)
> typeSyntaxCheckGoal env g = checkGoal env g

> bindType :: ModuleIdent -> TopDecl a -> TypeEnv -> TypeEnv
> bindType m (DataDecl _ _ tc _ cs _) =
>   globalBindTopEnv m tc (Data (qualifyWith m tc) xs)
>   where xs = map constr cs ++ nub (concatMap labels cs)
> bindType m (NewtypeDecl _ _ tc _ nc _) =
>   globalBindTopEnv m tc (Data (qualifyWith m tc) (nconstr nc : nlabel nc))
> bindType m (TypeDecl _ tc _ _) =
>   globalBindTopEnv m tc (Alias (qualifyWith m tc))
> bindType m (ClassDecl _ _ cls _ ds) =
>   globalBindTopEnv m cls (Class (qualifyWith m cls) (concatMap methods ds))
> bindType m (InstanceDecl _ _ _ _ _) = id
> bindType _ (DefaultDecl _ _) = id
> bindType _ (BlockDecl _) = id
> bindType _ (SplitAnnot _) = id

\end{verbatim}
The compiler allows anonymous type variables on the left hand side of
type declarations, but not on their right hand side. Function and
pattern declarations are traversed in order to check local type
signatures.
\begin{verbatim}

> checkTopDecl :: TypeEnv -> TopDecl a -> Error (TopDecl a)
> checkTopDecl env (DataDecl p cx tc tvs cs clss) =
>   do
>     cx' <- checkTypeLhs env p cx tvs
>     checkClosedContext p cx' tvs
>     cs' <-
>       liftE const (mapE (checkConstrDecl env tvs) cs) &&&
>       mapE_ (checkDClass env tvs) clss
>     return (DataDecl p cx' tc tvs cs' clss)
> checkTopDecl env (NewtypeDecl p cx tc tvs nc clss) =
>   do
>     cx' <- checkTypeLhs env p cx tvs
>     checkClosedContext p cx' tvs
>     nc' <-
>       liftE const (checkNewConstrDecl env tvs nc) &&&
>       mapE_ (checkDClass env tvs) clss
>     return (NewtypeDecl p cx' tc tvs nc' clss)
> checkTopDecl env (TypeDecl p tc tvs ty) =
>   do
>     checkTypeLhs env p [] tvs
>     ty' <- checkClosedType env p tvs ty
>     return (TypeDecl p tc tvs ty')
> checkTopDecl env (ClassDecl p cx cls tv ds) =
>   do
>     cx' <- checkTypeLhs env p cx [tv]
>     checkClosedContext p cx' [tv]
>     ds' <-
>       mapE_ (checkSimpleConstraint "class" doc p) cx' &&>
>       mapE (checkDecl env) ds
>     sequenceE_ [checkMethodType tv p ty | TypeSig p _ ty <- ds']
>     return (ClassDecl p cx' cls tv ds')
>   where doc = ppIdent cls <+> ppIdent tv
> checkTopDecl env (InstanceDecl p cx cls ty ds) =
>   do
>     (cx',ty') <- checkClass env p [] cls &&> checkInstType env p cx ty
>     ds' <-
>       mapE_ (checkSimpleConstraint "instance" doc p) cx' &&>
>       mapE (checkDecl env) ds
>     return (InstanceDecl p cx' cls ty' ds')
>   where doc = ppQIdent cls <+> ppTypeExpr 2 ty
> checkTopDecl env (DefaultDecl p tys) =
>   liftE (DefaultDecl p) (mapE (checkType env p []) tys)
> checkTopDecl env (BlockDecl d) = liftE BlockDecl (checkDecl env d)
> checkTopDecl _ (SplitAnnot p) = return (SplitAnnot p)

> checkDClass :: TypeEnv -> [Ident] -> DClass -> Error ()
> checkDClass env tvs (DClass p cls) = checkClass env p tvs cls

> checkGoal :: TypeEnv -> Goal a -> Error (Goal a)
> checkGoal env (Goal p e ds) =
>   liftE2 (Goal p) (checkExpr env p e) (mapE (checkDecl env) ds)

\end{verbatim}
Method type signatures have to obey a few additional restrictions.
The class type variable must appear in the method's type (otherwise,
the type would be inherently ambiguous), and the method's context must
not contain any additional constraints for that type variable
(cf.\ Sect.~4.3.1 of the Haskell report).
\begin{verbatim}

> checkMethodType :: Ident -> Position -> QualTypeExpr -> Error ()
> checkMethodType tv p ty =
>   do
>     unless (tv `elem` fv ty) (errorAt p (ambiguousType tv))
>     when (tv `elem` cvars ty) (errorAt p (constrainedClassType tv))
>   where cvars (QualTypeExpr cx _) = [cvar ty | ClassAssert _ ty <- cx]
>         cvar (VariableType tv) = tv
>         cvar (ApplyType ty _) = cvar ty

> checkDecl :: TypeEnv -> Decl a -> Error (Decl a)
> checkDecl _ (InfixDecl p fix pr ops) = return (InfixDecl p fix pr ops)
> checkDecl env (TypeSig p vs ty) =
>   liftE (TypeSig p vs) (checkQualType env p ty)
> checkDecl env (FunctionDecl p f eqs) =
>   liftE (FunctionDecl p f) (mapE (checkEquation env) eqs)
> checkDecl env (PatternDecl p t rhs) =
>   liftE (PatternDecl p t) (checkRhs env rhs)
> checkDecl env (ForeignDecl p fi f ty) =
>   liftE (ForeignDecl p fi f) (checkType env p [] ty)
> checkDecl _ (FreeDecl p vs) = return (FreeDecl p vs)
> checkDecl _ (TrustAnnot p tr fs) = return (TrustAnnot p tr fs)

> checkTypeLhs :: TypeEnv -> Position -> [ClassAssert] -> [Ident]
>              -> Error [ClassAssert]
> checkTypeLhs env p cx tvs =
>   mapE_ (errorAt p . nonLinear "left hand side of type declaration" . fst)
>         (duplicates (filter (anonId /=) tvs)) &&>
>   mapE (checkClassAssert env p tvs) cx

> checkSimpleConstraint :: String -> Doc -> Position -> ClassAssert -> Error ()
> checkSimpleConstraint what doc p (ClassAssert cls ty) =
>   unless (isVariableType ty)
>          (errorAt p (invalidSimpleConstraint what doc (ClassAssert cls ty)))

> checkConstrDecl :: TypeEnv -> [Ident] -> ConstrDecl -> Error ConstrDecl
> checkConstrDecl env tvs (ConstrDecl p evs cx c tys) =
>   do
>     cx' <- checkTypeLhs env p cx evs
>     checkClosedContext p cx' tvs'
>     tys' <- mapE (checkClosedType env p tvs') tys
>     return (ConstrDecl p evs cx' c tys')
>   where tvs' = evs ++ tvs
> checkConstrDecl env tvs (ConOpDecl p evs cx ty1 op ty2) =
>   do
>     cx' <- checkTypeLhs env p cx evs
>     checkClosedContext p cx' tvs'
>     (ty1',ty2') <-
>       liftE (,) (checkClosedType env p tvs' ty1) &&&
>       checkClosedType env p tvs' ty2
>     return (ConOpDecl p evs cx' ty1' op ty2')
>   where tvs' = evs ++ tvs
> checkConstrDecl env tvs (RecordDecl p evs cx c fs) =
>   do
>     cx' <- checkTypeLhs env p cx evs
>     checkClosedContext p cx' tvs'
>     fs' <- mapE (checkFieldDecl env tvs') fs
>     return (RecordDecl p evs cx' c fs')
>   where tvs' = evs ++ tvs

> checkFieldDecl :: TypeEnv -> [Ident] -> FieldDecl -> Error FieldDecl
> checkFieldDecl env tvs (FieldDecl p ls ty) =
>   liftE (FieldDecl p ls) (checkClosedType env p tvs ty)

> checkNewConstrDecl :: TypeEnv -> [Ident] -> NewConstrDecl
>                    -> Error NewConstrDecl
> checkNewConstrDecl env tvs (NewConstrDecl p c ty) =
>   liftE (NewConstrDecl p c) (checkClosedType env p tvs ty)
> checkNewConstrDecl env tvs (NewRecordDecl p c l ty) =
>   liftE (NewRecordDecl p c l) (checkClosedType env p tvs ty)

\end{verbatim}
Checking expressions is rather straightforward. The compiler must only
traverse the structure of expressions in order to find local
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
> checkExpr env p (Record a c fs) =
>   liftE (Record a c) (mapE (checkField env p) fs)
> checkExpr env p (RecordUpdate e fs) =
>   liftE2 RecordUpdate (checkExpr env p e) (mapE (checkField env p) fs)
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
> checkExpr env _ (Lambda p ts e) = liftE (Lambda p ts) (checkExpr env p e)
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
> checkExpr env p (Fcase e alts) =
>   liftE2 Fcase (checkExpr env p e) (mapE (checkAlt env) alts)

> checkStmt :: TypeEnv -> Position -> Statement a -> Error (Statement a)
> checkStmt env p (StmtExpr e) = liftE StmtExpr (checkExpr env p e)
> checkStmt env _ (StmtBind p t e) = liftE (StmtBind p t) (checkExpr env p e)
> checkStmt env _ (StmtDecl ds) = liftE StmtDecl (mapE (checkDecl env) ds)

> checkAlt :: TypeEnv -> Alt a -> Error (Alt a)
> checkAlt env (Alt p t rhs) = liftE (Alt p t) (checkRhs env rhs)

> checkField :: TypeEnv -> Position -> Field (Expression a)
>            -> Error (Field (Expression a))
> checkField env p (Field l e) = liftE (Field l) (checkExpr env p e)

\end{verbatim}
The parser cannot distinguish unqualified nullary type constructors
and type variables. Therefore, if the compiler finds an unbound
identifier in a position where a type variable is admissible, it will
interpret the identifier as such. In type declarations, type variables
on the left hand side of a declaration can shadow type constructors
with the same name.
\begin{verbatim}

> checkClosedType :: TypeEnv -> Position -> [Ident] -> TypeExpr
>                 -> Error TypeExpr
> checkClosedType env p tvs ty =
>   do
>     ty' <- checkType env p tvs ty
>     mapE_ (errorAt p . unboundVariable)
>           (nub (filter (\tv -> tv == anonId || tv `notElem` tvs) (fv ty')))
>     return ty'

> checkInstType :: TypeEnv -> Position -> [ClassAssert] -> TypeExpr
>               -> Error ([ClassAssert],TypeExpr)
> checkInstType env p cx ty =
>   do
>     QualTypeExpr cx' ty' <- checkQualType env p (QualTypeExpr cx ty)
>     unless (isSimpleType ty' && not (isTypeSynonym env (typeConstr ty')) &&
>             null (duplicates (filter (anonId /=) (fv ty'))))
>            (errorAt p (notSimpleType ty'))
>     return (cx',ty')

> checkQualType :: TypeEnv -> Position -> QualTypeExpr -> Error QualTypeExpr
> checkQualType env p (QualTypeExpr cx ty) =
>   do
>     (cx',ty') <-
>       liftE (,) (mapE (checkClassAssert env p []) cx) &&&
>       checkType env p [] ty
>     checkClosedContext p cx' (fv ty')
>     return (QualTypeExpr cx' ty')

> checkClassAssert :: TypeEnv -> Position -> [Ident] -> ClassAssert
>                  -> Error ClassAssert
> checkClassAssert env p tvs (ClassAssert cls ty) =
>   do
>     ty' <- checkClass env p tvs cls &&> checkType env p tvs ty
>     unless (isVariableType (root ty'))
>            (errorAt p (invalidConstraint (ClassAssert cls ty')))
>     return (ClassAssert cls ty')
>   where root (ApplyType ty _) = root ty
>         root ty = ty

> checkClosedContext :: Position -> [ClassAssert] -> [Ident] -> Error ()
> checkClosedContext p cx tvs =
>   mapE_ (errorAt p . unboundVariable) (nub (filter (`notElem` tvs) (fv cx)))

> checkType :: TypeEnv -> Position -> [Ident] -> TypeExpr -> Error TypeExpr
> checkType env p tvs (ConstructorType tc)
>   | tc `elem` map qualify tvs = return (VariableType (unqualify tc))
>   | otherwise =
>       case qualLookupTopEnv tc env of
>         []
>           | isQualified tc -> errorAt p (undefinedType tc)
>           | otherwise -> return (VariableType (unqualify tc))
>         [Data _ _] -> return (ConstructorType tc)
>         [Alias _] -> return (ConstructorType tc)
>         [Class _ _] -> errorAt p (undefinedType tc)
>         rs -> errorAt p (ambiguousIdent rs tc)
> checkType env p tvs (VariableType tv)
>   | tv `elem` anonId:tvs = return (VariableType tv)
>   | otherwise = checkType env p tvs (ConstructorType (qualify tv))
> checkType env p tvs (TupleType tys) =
>   liftE TupleType (mapE (checkType env p tvs) tys)
> checkType env p tvs (ListType ty) =
>   liftE ListType (checkType env p tvs ty)
> checkType env p tvs (ArrowType ty1 ty2) =
>   liftE2 ArrowType (checkType env p tvs ty1) (checkType env p tvs ty2)
> checkType env p tvs (ApplyType ty1 ty2) =
>   liftE2 ApplyType (checkType env p tvs ty1) (checkType env p tvs ty2)

> checkClass :: TypeEnv -> Position -> [Ident] -> QualIdent -> Error ()
> checkClass env p tvs cls
>   | cls `elem` map qualify tvs = errorAt p (undefinedClass cls)
>   | otherwise =
>       case qualLookupTopEnv cls env of
>         [] -> errorAt p (undefinedClass cls)
>         [Data _ _] -> errorAt p (undefinedClass cls)
>         [Alias _] -> errorAt p (undefinedClass cls)
>         [Class _ _] -> return ()
>         rs -> errorAt p (ambiguousIdent rs cls)

\end{verbatim}
The compiler reports an error when more than one instance is defined
for a particular pair of a type class and type constructor. This
includes duplicate instances defined in the current module as well as
conflicts between locally defined instances and imported instances.
\begin{verbatim}

> checkInstances :: TypeEnv -> InstSet -> [TopDecl a] -> Error ()
> checkInstances tEnv iEnv ds =
>   do
>     sequenceE_ [errorAt p (duplicateInstance (unqualCT tEnv inst))
>                | P p inst <- unique cts, inst `elemSet` iEnv] &&>
>       reportDuplicates (duplicateInstance . unqualCT tEnv)
>                        (repeatedInstance . unqualCT tEnv) cts
>     return ()
>   where cts = map (fmap (qualCT tEnv)) (concatMap instances ds)
>         unique [] = []
>         unique (x:xs)
>           | x `elem` xs = unique (filter (x /=) xs)
>           | otherwise = x : unique xs

> bindInstance :: P CT -> InstSet -> InstSet
> bindInstance (P _ inst) iEnv = addToSet inst iEnv

> qualCT :: TypeEnv -> CT -> CT
> qualCT env (CT cls tc) = CT (qual env cls) (qual env tc)
>   where qual env x = origName (head (qualLookupTopEnv x env))

> unqualCT :: TypeEnv -> CT -> CT
> unqualCT env (CT cls tc) = CT (unqual env cls) (unqual env tc)
>   where unqual env x =
>           case lookupTopEnv x' env of
>             [y] | origName y == x -> qualify x'
>             _ -> x
>           where x' = unqualify x

\end{verbatim}
Auxiliary definitions.
\begin{verbatim}

> tident :: TopDecl a -> P Ident
> tident (DataDecl p _ tc _ _ _) = P p tc
> tident (NewtypeDecl p _ tc _ _ _) = P p tc
> tident (TypeDecl p tc _ _) = P p tc
> tident (ClassDecl p _ cls _ _) = P p cls
> tident (InstanceDecl _ _ _ _ _) = internalError "tident"
> tident (DefaultDecl _ _) = internalError "tident"
> tident (BlockDecl _) = internalError "tident"
> tident (SplitAnnot _) = internalError "tident"

> instances :: TopDecl a -> [P CT]
> instances (DataDecl _ _ tc _ _ clss) =
>   [P p (CT cls (qualify tc)) | DClass p cls <- clss]
> instances (NewtypeDecl _ _ tc _ _ clss) =
>   [P p (CT cls (qualify tc)) | DClass p cls <- clss]
> instances (TypeDecl _ _ _ _) = []
> instances (ClassDecl _ _ _ _ _) = []
> instances (InstanceDecl p _ cls ty _) = [P p (CT cls (typeConstr ty))]
> instances (DefaultDecl _ _) = []
> instances (BlockDecl _) = []
> instances (SplitAnnot _) = []

> isTypeSynonym :: TypeEnv -> QualIdent -> Bool
> isTypeSynonym env tc =
>   case qualLookupTopEnv tc env of
>     [Data _ _] -> False
>     [Alias _] -> True
>     _ -> internalError "isTypeSynonym"

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

> duplicateDefault :: String
> duplicateDefault = "More than one default declaration"

> repeatedDefault :: String
> repeatedDefault = "Repeated default declaration"

> nonLinear :: String -> Ident -> String
> nonLinear what tv =
>   "Type variable " ++ name tv ++ " occurs more than once in " ++ what

> unboundVariable :: Ident -> String
> unboundVariable tv = "Undefined type variable " ++ name tv

> ambiguousType :: Ident -> String
> ambiguousType tv =
>   "Method type does not mention type variable " ++ name tv

> constrainedClassType :: Ident -> String
> constrainedClassType tv =
>   "Method type context must not constrain type variable " ++ name tv

> invalidSimpleConstraint :: String -> Doc -> ClassAssert -> String
> invalidSimpleConstraint what doc ca = show $
>   vcat [text "Illegal class constraint" <+> ppClassAssert ca,
>         text "in" <+> text what <+> text "declaration" <+> doc,
>         text "Constraints in class and instance declarations must be of the",
>         text "form C u, where u is a type variable."]

> invalidConstraint :: ClassAssert -> String
> invalidConstraint ca = show $
>   vcat [text "Illegal class constraint" <+> ppClassAssert ca,
>         text "Constraints must be of the form C u or C (u t1 ... tn),",
>         text "where u is a type variable and t1, ..., tn are types."]

> notSimpleType :: TypeExpr -> String
> notSimpleType ty = show $
>   vcat [text "Illegal instance type" <+> ppTypeExpr 0 ty,
>         text "The instance type must be of the form (T u1 ... un),",
>         text "where T is not a type synonym and u1, ..., un are",
>         text "mutually distinct type variables."]

\end{verbatim}
