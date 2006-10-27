% -*- LaTeX -*-
% $Id: IntfSyntaxCheck.lhs 1984 2006-10-27 13:34:07Z wlux $
%
% Copyright (c) 2000-2006, Wolfgang Lux
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
> bindType (HidingDataDecl _ tc _) = qualBindTopEnv tc (Data tc [])
> bindType (IDataDecl _ tc _ cs) =
>   qualBindTopEnv tc (Data tc (map constr (catMaybes cs)))
> bindType (INewtypeDecl _ tc _ nc) = qualBindTopEnv tc (Data tc [nconstr nc])
> bindType (ITypeDecl _ tc _ _) = qualBindTopEnv tc (Alias tc)
> bindType (HidingClassDecl _ cls _) = qualBindTopEnv cls (Class cls)
> bindType (IClassDecl _ cls _) = qualBindTopEnv cls (Class cls)
> bindType (IInstanceDecl _ _ _) = id
> bindType (IFunctionDecl _ _ _) = id

\end{verbatim}
The checks applied to the interface are similar to those performed
during syntax checking of type expressions.
\begin{verbatim}

> checkIDecl :: TypeEnv -> IDecl -> Error IDecl
> checkIDecl _ (IInfixDecl p fix pr op) = return (IInfixDecl p fix pr op)
> checkIDecl env (HidingDataDecl p tc tvs) =
>   checkTypeLhs env p tvs &&>
>   return (HidingDataDecl p tc tvs)
> checkIDecl env (IDataDecl p tc tvs cs) =
>   checkTypeLhs env p tvs &&>
>   liftE (IDataDecl p tc tvs) (mapE (liftMaybe (checkConstrDecl env tvs)) cs)
> checkIDecl env (INewtypeDecl p tc tvs nc) =
>   checkTypeLhs env p tvs &&>
>   liftE (INewtypeDecl p tc tvs) (checkNewConstrDecl env tvs nc)
> checkIDecl env (ITypeDecl p tc tvs ty) =
>   checkTypeLhs env p tvs &&>
>   liftE (ITypeDecl p tc tvs) (checkClosedType env p tvs ty)
> checkIDecl env (HidingClassDecl p cls tv) =
>   do
>     checkTypeLhs env p [tv]
>     return (HidingClassDecl p cls tv)
> checkIDecl env (IClassDecl p cls tv) =
>   do
>     checkTypeLhs env p [tv]
>     return (IClassDecl p cls tv)
> checkIDecl env (IInstanceDecl p cls ty) =
>   checkClass env p cls &&>
>   liftE (IInstanceDecl p cls) (checkSimpleType env p ty)
> checkIDecl env (IFunctionDecl p f ty) =
>   liftE (IFunctionDecl p f) (checkQualType env p ty)

> checkTypeLhs :: TypeEnv -> Position -> [Ident] -> Error ()
> checkTypeLhs env p tvs =
>   mapE_ (errorAt p . noVariable "left hand side of type declaration")
>         (nub tcs) &&>
>   mapE_ (errorAt p . nonLinear . fst) (duplicates tvs')
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

> checkClosedType :: TypeEnv -> Position -> [Ident] -> TypeExpr
>                 -> Error TypeExpr
> checkClosedType env p tvs ty =
>   do
>     ty' <- checkType env p ty
>     mapE_ (errorAt p . unboundVariable)
>           (nub (filter (`notElem` tvs) (fv ty')))
>     return ty'

> checkQualType :: TypeEnv -> Position -> QualTypeExpr -> Error QualTypeExpr
> checkQualType env p (QualTypeExpr cx ty) =
>   do
>     ty' <- mapE_ (checkClassAssert env p) cx &&> checkType env p ty
>     let tvs = fv ty'
>     mapE_ (errorAt p . unboundVariable)
>           (nub [tv | ClassAssert _ tv <- cx, tv `notElem` tvs])
>     return (QualTypeExpr cx ty')

> checkClassAssert :: TypeEnv -> Position -> ClassAssert -> Error ()
> checkClassAssert env p (ClassAssert cls tv) =
>   checkClass env p cls &&>
>   unless (null (lookupTopEnv tv env))
>          (errorAt p (noVariable "class assertion" tv))

> checkType :: TypeEnv -> Position -> TypeExpr -> Error TypeExpr
> checkType env p (ConstructorType tc tys) =
>   liftE2 ($)
>          (case qualLookupTopEnv tc env of
>             []
>               | not (isQualified tc) && null tys ->
>                   return (const (VariableType (unqualify tc)))
>               | otherwise -> errorAt p (undefinedType tc)
>             [Data _ _] -> return (ConstructorType tc)
>             [Alias _] -> errorAt p (badTypeSynonym tc)
>             [Class _] -> errorAt p (undefinedType tc)
>             _ -> internalError "checkType")
>          (mapE (checkType env p) tys)
> checkType env p (VariableType tv) =
>   checkType env p (ConstructorType (qualify tv) [])
> checkType env p (TupleType tys) = liftE TupleType (mapE (checkType env p) tys)
> checkType env p (ListType ty) = liftE ListType (checkType env p ty)
> checkType env p (ArrowType ty1 ty2) =
>   liftE2 ArrowType (checkType env p ty1) (checkType env p ty2)

> checkSimpleType :: TypeEnv -> Position -> TypeExpr -> Error TypeExpr
> checkSimpleType env p ty =
>   do
>     ty' <- checkType env p ty
>     unless (isSimpleType ty' && not (isTypeSynonym env (root ty')) &&
>             null (duplicates (fv ty')))
>            (errorAt p (notSimpleType ty'))
>     return ty'

> checkClass :: TypeEnv -> Position -> QualIdent -> Error ()
> checkClass env p cls =
>   case qualLookupTopEnv cls env of
>     [] -> errorAt p (undefinedClass cls)
>     [Data _ _] -> errorAt p (undefinedClass cls)
>     [Alias _] -> errorAt p (undefinedClass cls)
>     [Class _] -> return ()
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

> notSimpleType :: TypeExpr -> String
> notSimpleType ty = show $
>   vcat [text "Illegal instance type" <+> ppTypeExpr 0 ty,
>         text "The instance type must be of the form (T a b c), where T is",
>         text "not a type synonym and a, b, c are distinct type variables."]

\end{verbatim}
