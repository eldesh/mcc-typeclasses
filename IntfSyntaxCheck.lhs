% -*- LaTeX -*-
% $Id: IntfSyntaxCheck.lhs 2452 2007-08-23 22:51:27Z wlux $
%
% Copyright (c) 2000-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{IntfSyntaxCheck.lhs}
\section{Checking Interface Declarations}
Similar to Curry source files, some post-processing has to be applied
to parsed interface files. In particular, the compiler must
disambiguate nullary type constructors and type variables. In
addition, the compiler also checks that all type constructor
applications are saturated. Since interface files are closed -- i.e.,
they include declarations of all types and classes which are defined
in other modules and used in the interface -- the compiler can perform
this check without reference to the global environments.
\begin{verbatim}

> module IntfSyntaxCheck(intfSyntaxCheck) where
> import Base
> import CurryPP
> import Error
> import List
> import Maybe
> import Monad
> import Pretty
> import TopEnv

> intfSyntaxCheck :: [IDecl] -> Error [IDecl]
> intfSyntaxCheck ds = mapE (checkIDecl env) ds
>   where env = foldr bindType (fmap typeKind initTCEnv) ds

\end{verbatim}
The compiler requires information about the arity of each defined type
constructor as well as information whether the type constructor
denotes an algebraic data type, a renaming type, or a type synonym.
The latter must not occur in type expressions in interfaces.
\begin{verbatim}

> bindType :: IDecl -> TypeEnv -> TypeEnv
> bindType (IInfixDecl _ _ _ _) = id
> bindType (HidingDataDecl _ tc _ _) = qualBindTopEnv tc (Data tc [])
> bindType (IDataDecl _ _ tc _ _ cs) =
>   qualBindTopEnv tc (Data tc (map constr (catMaybes cs)))
> bindType (INewtypeDecl _ _ tc _ _ nc) =
>   qualBindTopEnv tc (Data tc [nconstr nc])
> bindType (ITypeDecl _ tc _ _ _) = qualBindTopEnv tc (Alias tc)
> bindType (HidingClassDecl _ _ cls _ _) = qualBindTopEnv cls (Class cls [])
> bindType (IClassDecl _ cx cls _ _ ds) =
>   qualBindTopEnv cls (Class cls (map imethod (catMaybes ds)))
> bindType (IInstanceDecl _ _ _ _ _) = id
> bindType (IFunctionDecl _ _ _ _) = id

\end{verbatim}
The checks applied to the interface are similar to those performed
during syntax checking of type expressions.
\begin{verbatim}

> checkIDecl :: TypeEnv -> IDecl -> Error IDecl
> checkIDecl _ (IInfixDecl p fix pr op) = return (IInfixDecl p fix pr op)
> checkIDecl env (HidingDataDecl p tc k tvs) =
>   do
>     checkTypeLhs env p [] tvs
>     return (HidingDataDecl p tc k tvs)
> checkIDecl env (IDataDecl p cx tc k tvs cs) =
>   do
>     cx' <- checkTypeLhs env p cx tvs
>     checkClosedContext p cx' tvs
>     cs' <- mapE (liftMaybe (checkConstrDecl env tvs)) cs
>     return (IDataDecl p cx' tc k tvs cs')
> checkIDecl env (INewtypeDecl p cx tc k tvs nc) =
>   do
>     cx' <- checkTypeLhs env p cx tvs
>     checkClosedContext p cx' tvs
>     nc' <- checkNewConstrDecl env tvs nc
>     return (INewtypeDecl p cx' tc k tvs nc')
> checkIDecl env (ITypeDecl p tc k tvs ty) =
>   do
>     checkTypeLhs env p [] tvs
>     ty' <- checkClosedType env p tvs ty
>     return (ITypeDecl p tc k tvs ty')
> checkIDecl env (HidingClassDecl p cx cls k tv) =
>   do
>     cx' <- checkTypeLhs env p cx [tv]
>     checkClosedContext p cx' [tv]
>     mapE_ (checkSimpleConstraint "class" doc p) cx'
>     return (HidingClassDecl p cx' cls k tv)
>   where doc = ppQIdent cls <+> ppIdent tv
> checkIDecl env (IClassDecl p cx cls k tv ds) =
>   do
>     cx' <- checkTypeLhs env p cx [tv]
>     checkClosedContext p cx' [tv]
>     ds' <-
>       mapE_ (checkSimpleConstraint "class" doc p) cx' &&>
>       mapE (liftMaybe (checkIMethodDecl env tv)) ds
>     return (IClassDecl p cx' cls k tv ds')
>   where doc = ppQIdent cls <+> ppIdent tv
> checkIDecl env (IInstanceDecl p cx cls ty m) =
>   do
>     (cx',ty') <- checkClass env p cls &&> checkInstType env p cx ty
>     mapE_ (checkSimpleConstraint "instance" doc p) cx
>     return (IInstanceDecl p cx' cls ty' m)
>   where doc = ppQIdent cls <+> ppTypeExpr 2 ty
> checkIDecl env (IFunctionDecl p f n ty) =
>   maybe (return ()) (checkArity p) n &&>
>   liftE (IFunctionDecl p f n) (checkQualType env p ty)
>   where checkArity p n =
>           unless (n < toInteger (maxBound::Int)) (errorAt p (arityTooBig n))

> checkTypeLhs :: TypeEnv -> Position -> [ClassAssert] -> [Ident]
>              -> Error [ClassAssert]
> checkTypeLhs env p cx tvs =
>   mapE_ (errorAt p . noVariable "left hand side of type declaration")
>         (nub tcs) &&>
>   mapE_ (errorAt p . nonLinear . fst) (duplicates tvs') &&>
>   mapE (checkClassAssert env p) cx
>   where (tcs,tvs') = partition isTypeConstr tvs
>         isTypeConstr tv = not (null (lookupTopEnv tv env))

> checkSimpleConstraint :: String -> Doc -> Position -> ClassAssert -> Error ()
> checkSimpleConstraint what doc p (ClassAssert cls tv tys) =
>   unless (null tys)
>          (errorAt p (invalidConstraint what doc (ClassAssert cls tv tys)))

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

> checkNewConstrDecl :: TypeEnv -> [Ident] -> NewConstrDecl
>                    -> Error NewConstrDecl
> checkNewConstrDecl env tvs (NewConstrDecl p c ty) =
>   liftE (NewConstrDecl p c) (checkClosedType env p tvs ty)

> checkIMethodDecl :: TypeEnv -> Ident -> IMethodDecl -> Error IMethodDecl
> checkIMethodDecl env tv (IMethodDecl p f ty) =
>   do
>     ty' <- checkQualType env p ty
>     unless (tv `elem` fv ty') (errorAt p (ambiguousType tv))
>     when (tv `elem` constrainedVars ty') (errorAt p (constrainedClassType tv))
>     return (IMethodDecl p f ty')
>   where constrainedVars (QualTypeExpr cx _) = [tv | ClassAssert _ tv _ <- cx]

> checkClosedType :: TypeEnv -> Position -> [Ident] -> TypeExpr
>                 -> Error TypeExpr
> checkClosedType env p tvs ty =
>   do
>     ty' <- checkType env p ty
>     mapE_ (errorAt p . unboundVariable)
>           (nub (filter (`notElem` tvs) (fv ty')))
>     return ty'

> checkInstType :: TypeEnv -> Position -> [ClassAssert] -> TypeExpr
>               -> Error ([ClassAssert],TypeExpr)
> checkInstType env p cx ty =
>   do
>     QualTypeExpr cx' ty' <- checkQualType env p (QualTypeExpr cx ty)
>     unless (isSimpleType ty' && not (isTypeSynonym env (root ty')) &&
>             null (duplicates (fv ty')))
>            (errorAt p (notSimpleType ty'))
>     return (cx',ty')

> checkQualType :: TypeEnv -> Position -> QualTypeExpr -> Error QualTypeExpr
> checkQualType env p (QualTypeExpr cx ty) =
>   do
>     (cx',ty') <-
>       liftE (,) (mapE (checkClassAssert env p) cx) &&& checkType env p ty
>     checkClosedContext p cx' (fv ty')
>     return (QualTypeExpr cx' ty')

> checkClassAssert :: TypeEnv -> Position -> ClassAssert -> Error ClassAssert
> checkClassAssert env p (ClassAssert cls tv tys) =
>   checkClass env p cls &&>
>   unless (null (lookupTopEnv tv env))
>          (errorAt p (noVariable "class constraint" tv)) &&>
>   liftE (ClassAssert cls tv) (mapE (checkType env p) tys)

> checkClosedContext :: Position -> [ClassAssert] -> [Ident] -> Error ()
> checkClosedContext p cx tvs =
>   mapE_ (errorAt p . unboundVariable) (nub (filter (`notElem` tvs) (fv cx)))

> checkType :: TypeEnv -> Position -> TypeExpr -> Error TypeExpr
> checkType env p (ConstructorType tc) =
>   case qualLookupTopEnv tc env of
>     []
>       | isQualified tc -> errorAt p (undefinedType tc)
>       | otherwise -> return (VariableType (unqualify tc))
>     [Data _ _] -> return (ConstructorType tc)
>     [Alias _] -> errorAt p (badTypeSynonym tc)
>     [Class _ _] -> errorAt p (undefinedType tc)
>     _ -> internalError "checkType"
> checkType env p (VariableType tv) =
>   checkType env p (ConstructorType (qualify tv))
> checkType env p (TupleType tys) = liftE TupleType (mapE (checkType env p) tys)
> checkType env p (ListType ty) = liftE ListType (checkType env p ty)
> checkType env p (ArrowType ty1 ty2) =
>   liftE2 ArrowType (checkType env p ty1) (checkType env p ty2)
> checkType env p (ApplyType ty1 ty2) =
>   liftE2 ApplyType (checkType env p ty1) (checkType env p ty2)

> checkClass :: TypeEnv -> Position -> QualIdent -> Error ()
> checkClass env p cls =
>   case qualLookupTopEnv cls env of
>     [] -> errorAt p (undefinedClass cls)
>     [Data _ _] -> errorAt p (undefinedClass cls)
>     [Alias _] -> errorAt p (undefinedClass cls)
>     [Class _ _] -> return ()
>     _ -> internalError "checkClass"

\end{verbatim}
\ToDo{Much of the above code could be shared with module
  \texttt{TypeSyntaxCheck}.}

Auxiliary functions.
\begin{verbatim}

> liftMaybe :: Monad m => (a -> m b) -> Maybe a -> m (Maybe b)
> liftMaybe f (Just x) = liftM Just (f x)
> liftMaybe f Nothing = return Nothing

> isSimpleType :: TypeExpr -> Bool
> isSimpleType (ConstructorType _) = True
> isSimpleType (VariableType _) = False
> isSimpleType (TupleType tys) = all isVariableType tys
> isSimpleType (ListType ty) = isVariableType ty
> isSimpleType (ArrowType ty1 ty2) = isVariableType ty1 && isVariableType ty2
> isSimpleType (ApplyType ty1 ty2) = isSimpleType ty1 && isVariableType ty2

> isTypeSynonym :: TypeEnv -> QualIdent -> Bool
> isTypeSynonym env tc =
>   case qualLookupTopEnv tc env of
>     [Data _ _] -> False
>     [Alias _] -> True
>     _ -> internalError "isTypeSynonym"

> isVariableType :: TypeExpr -> Bool
> isVariableType (ConstructorType _) = False
> isVariableType (VariableType _) = True
> isVariableType (TupleType _) = False
> isVariableType (ListType _) = False
> isVariableType (ArrowType _ _) = False
> isVariableType (ApplyType _ _) = False

> root :: TypeExpr -> QualIdent
> root (ConstructorType tc) = tc
> root (VariableType _) = internalError "root"
> root (TupleType tys) = qTupleId (length tys)
> root (ListType _) = qListId
> root (ArrowType _ _) = qArrowId
> root (ApplyType ty _) = root ty

\end{verbatim}
Error messages.
\begin{verbatim}

> undefinedType :: QualIdent -> String
> undefinedType tc = "Undefined type " ++ qualName tc

> undefinedClass :: QualIdent -> String
> undefinedClass cls = "Undefined type class " ++ qualName cls

> nonLinear :: Ident -> String
> nonLinear tv =
>   "Type variable " ++ name tv ++
>   " occurs more than once on left hand side of type declaration"

> noVariable :: String -> Ident -> String
> noVariable what tv =
>   "Type constructor or type class " ++ name tv ++ " used in " ++ what

> unboundVariable :: Ident -> String
> unboundVariable tv = "Undefined type variable " ++ name tv

> badTypeSynonym :: QualIdent -> String
> badTypeSynonym tc = "Synonym type " ++ qualName tc ++ " in interface"

> ambiguousType :: Ident -> String
> ambiguousType tv =
>   "Method type does not mention type variable " ++ name tv

> constrainedClassType :: Ident -> String
> constrainedClassType tv =
>   "Method type context must not constrain type variable " ++ name tv

> invalidConstraint :: String -> Doc -> ClassAssert -> String
> invalidConstraint what doc ca = show $
>   vcat [text "Illegal class constraint" <+> ppClassAssert ca,
>         text "in" <+> text what <+> text "declaration" <+> doc,
>         text "Constraints in class and instance declarations must be of the",
>         text "form C u, where u is a type variable."]

> notSimpleType :: TypeExpr -> String
> notSimpleType ty = show $
>   vcat [text "Illegal instance type" <+> ppTypeExpr 0 ty,
>         text "The instance type must be of the form (T a b c), where T is",
>         text "not a type synonym and a, b, c are distinct type variables."]

> arityTooBig :: Integer -> String
> arityTooBig n = "Function arity out of range: " ++ show n

\end{verbatim}
