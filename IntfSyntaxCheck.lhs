% -*- LaTeX -*-
% $Id: IntfSyntaxCheck.lhs 3225 2016-06-16 08:40:29Z wlux $
%
% Copyright (c) 2000-2015, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{IntfSyntaxCheck.lhs}
\section{Checking Interface Declarations}
Similar to Curry source files, some post-processing has to be applied
to parsed interface files. In particular, the compiler must
disambiguate nullary type constructors and type variables. In
addition, the compiler also checks that all type constructor
applications are saturated. Since interface files are closed -- i.e.,
they include declarations of all entities which are defined in other
modules\footnote{Strictly speaking this is not true. The unit, list,
  and tuple types are available in all modules but are included only
  in the interface of the Prelude, which contains the definitions of
  these types.} -- the compiler can perform this check without
reference to the global environments.
\begin{verbatim}

> module IntfSyntaxCheck(intfSyntaxCheck) where
> import Applicative
> import Base
> import Curry
> import CurryPP
> import CurryUtils
> import Error
> import IdentInfo
> import List
> import Monad
> import Pretty
> import PredefIdent
> import TopEnv
> import Utils

\end{verbatim}
The compiler requires information about the arity of each defined type
constructor as well as information whether the type constructor
denotes an algebraic data type, a renaming type, or a type synonym.
The latter must not occur in type expressions in interfaces.
\begin{verbatim}

> intfSyntaxCheck :: [IDecl] -> Error [IDecl]
> intfSyntaxCheck ds = mapA (checkIDecl env) ds
>   where env = foldr bindType initTEnv (concatMap tidents (map unhide ds))
>         bindType t = qualBindTopEnv (origName t) t

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
> checkIDecl env (IDataDecl p cx tc k tvs cs xs) =
>   do
>     cx' <- checkTypeLhs env p cx tvs
>     checkClosedContext p cx' tvs
>     cs' <- mapA (checkConstrDecl env tvs) cs
>     checkHiding True p tc (map constr cs ++ nub (concatMap labels cs)) xs
>     return (IDataDecl p cx' tc k tvs cs' xs)
> checkIDecl env (INewtypeDecl p cx tc k tvs nc xs) =
>   do
>     cx' <- checkTypeLhs env p cx tvs
>     checkClosedContext p cx' tvs
>     nc' <- checkNewConstrDecl env tvs nc
>     checkHiding True p tc (nconstr nc : nlabel nc) xs
>     return (INewtypeDecl p cx' tc k tvs nc' xs)
> checkIDecl env (ITypeDecl p tc k tvs ty) =
>   do
>     checkTypeLhs env p [] tvs
>     ty' <- checkClosedType env p tvs ty
>     return (ITypeDecl p tc k tvs ty')
> checkIDecl env (HidingClassDecl p cx cls k tv) =
>   do
>     cx' <- checkTypeLhs env p cx [tv]
>     checkClosedContext p cx' [tv]
>     mapA_ (checkSimpleConstraint "class" doc p) cx'
>     return (HidingClassDecl p cx' cls k tv)
>   where doc = ppQIdent cls <+> ppIdent tv
> checkIDecl env (IClassDecl p cx cls k tv ds fs') =
>   do
>     cx' <- checkTypeLhs env p cx [tv]
>     checkClosedContext p cx' [tv]
>     ds' <-
>       mapA_ (checkSimpleConstraint "class" doc p) cx' *>
>       mapA (checkIMethodDecl env tv) ds
>     checkHiding False p cls (map imethod ds) fs'
>     return (IClassDecl p cx' cls k tv ds' fs')
>   where doc = ppQIdent cls <+> ppIdent tv
> checkIDecl env (IInstanceDecl p cx cls ty m fs) =
>   do
>     (cx',ty') <- checkClass env p [] cls *> checkInstType env p cx ty
>     mapA_ (checkSimpleConstraint "instance" doc p) cx *>
>       mapA_ (errorAt p . multipleArity . fst) (duplicates (map fst fs))
>     return (IInstanceDecl p cx' cls ty' m fs)
>   where doc = ppQIdent cls <+> ppTypeExpr 2 ty
> checkIDecl env (IFunctionDecl p f n ty) =
>   maybe (return ()) (checkArity p) n *>
>   liftA (IFunctionDecl p f n) (checkQualType env p ty)
>   where checkArity p n =
>           unless (n < toInteger (maxBound::Int)) (errorAt p (arityTooBig n))

> checkTypeLhs :: TypeEnv -> Position -> [ClassAssert] -> [Ident]
>              -> Error [ClassAssert]
> checkTypeLhs env p cx tvs =
>   mapA_ (errorAt p . nonLinear . fst) (duplicates tvs) *>
>   mapA (checkClassAssert env p tvs) cx

> checkSimpleConstraint :: String -> Doc -> Position -> ClassAssert -> Error ()
> checkSimpleConstraint what doc p (ClassAssert cls ty) =
>   unless (isVariableType ty)
>          (errorAt p (invalidSimpleConstraint what doc (ClassAssert cls ty)))

> checkConstrDecl :: TypeEnv -> [Ident] -> ConstrDecl -> Error ConstrDecl
> checkConstrDecl env tvs (ConstrDecl p evs cx c tys) =
>   do
>     cx' <- checkTypeLhs env p cx evs
>     checkClosedContext p cx' tvs'
>     tys' <- mapA (checkClosedType env p tvs') tys
>     return (ConstrDecl p evs cx' c tys')
>   where tvs' = evs ++ tvs
> checkConstrDecl env tvs (ConOpDecl p evs cx ty1 op ty2) =
>   do
>     cx' <- checkTypeLhs env p cx evs
>     checkClosedContext p cx' tvs'
>     (ty1',ty2') <-
>       liftA (,) (checkClosedType env p tvs' ty1) <*>
>       checkClosedType env p tvs' ty2
>     return (ConOpDecl p evs cx' ty1' op ty2')
>   where tvs' = evs ++ tvs
> checkConstrDecl env tvs (RecordDecl p evs cx c fs) =
>   do
>     cx' <- checkTypeLhs env p cx evs
>     checkClosedContext p cx' tvs'
>     fs' <- mapA (checkFieldDecl env tvs') fs
>     return (RecordDecl p evs cx' c fs')
>   where tvs' = evs ++ tvs

> checkFieldDecl :: TypeEnv -> [Ident] -> FieldDecl -> Error FieldDecl
> checkFieldDecl env tvs (FieldDecl p ls ty) =
>   liftA (FieldDecl p ls) (checkClosedType env p tvs ty)

> checkNewConstrDecl :: TypeEnv -> [Ident] -> NewConstrDecl
>                    -> Error NewConstrDecl
> checkNewConstrDecl env tvs (NewConstrDecl p c ty) =
>   liftA (NewConstrDecl p c) (checkClosedType env p tvs ty)
> checkNewConstrDecl env tvs (NewRecordDecl p c l ty) =
>   liftA (NewRecordDecl p c l) (checkClosedType env p tvs ty)

> checkIMethodDecl :: TypeEnv -> Ident -> IMethodDecl -> Error IMethodDecl
> checkIMethodDecl env tv (IMethodDecl p f n ty) =
>   do
>     ty' <- checkQualType env p ty
>     unless (tv `elem` fv ty') (errorAt p (ambiguousType tv))
>     when (tv `elem` cvars ty') (errorAt p (constrainedClassType tv))
>     return (IMethodDecl p f n ty')
>   where cvars (QualTypeExpr cx _) = [cvar ty | ClassAssert _ ty <- cx]
>         cvar (VariableType tv) = tv
>         cvar (ApplyType ty _) = cvar ty

> checkClosedType :: TypeEnv -> Position -> [Ident] -> TypeExpr
>                 -> Error TypeExpr
> checkClosedType env p tvs ty =
>   do
>     ty' <- checkType env p tvs ty
>     mapA_ (errorAt p . unboundVariable)
>           (nub (filter (`notElem` tvs) (fv ty')))
>     return ty'

> checkInstType :: TypeEnv -> Position -> [ClassAssert] -> TypeExpr
>               -> Error ([ClassAssert],TypeExpr)
> checkInstType env p cx ty =
>   do
>     QualTypeExpr cx' ty' <- checkQualType env p (QualTypeExpr cx ty)
>     unless (isSimpleType ty' && not (isTypeSynonym env (typeConstr ty')) &&
>             null (duplicates (fv ty')))
>            (errorAt p (notSimpleType ty'))
>     return (cx',ty')

> checkQualType :: TypeEnv -> Position -> QualTypeExpr -> Error QualTypeExpr
> checkQualType env p (QualTypeExpr cx ty) =
>   do
>     (cx',ty') <-
>       liftA (,) (mapA (checkClassAssert env p []) cx) <*>
>       checkType env p [] ty
>     checkClosedContext p cx' (fv ty')
>     return (QualTypeExpr cx' ty')

> checkClassAssert :: TypeEnv -> Position -> [Ident] -> ClassAssert
>                  -> Error ClassAssert
> checkClassAssert env p tvs (ClassAssert cls ty) =
>   do
>     ty' <- checkClass env p tvs cls *> checkType env p tvs ty
>     unless (isVariableType (root ty'))
>            (errorAt p (invalidConstraint (ClassAssert cls ty')))
>     return (ClassAssert cls ty')
>   where root (ApplyType ty _) = root ty
>         root ty = ty

> checkClosedContext :: Position -> [ClassAssert] -> [Ident] -> Error ()
> checkClosedContext p cx tvs =
>   mapA_ (errorAt p . unboundVariable) (nub (filter (`notElem` tvs) (fv cx)))

> checkType :: TypeEnv -> Position -> [Ident] -> TypeExpr -> Error TypeExpr
> checkType env p tvs (ConstructorType tc)
>   | tc `elem` map qualify tvs = return (VariableType (unqualify tc))
>   | otherwise =
>       case qualLookupTopEnv tc env of
>         []
>           | isPrimTypeId tc' -> return (ConstructorType tc)
>           | isQualified tc -> errorAt p (undefinedType tc)
>           | otherwise -> return (VariableType tc')
>           where tc' = unqualify tc
>         [Data _ _] -> return (ConstructorType tc)
>         [Alias _] -> errorAt p (badTypeSynonym tc)
>         [Class _ _] -> errorAt p (undefinedType tc)
>         _ -> internalError "checkType"
> checkType env p tvs (VariableType tv)
>   | tv `elem` tvs = return (VariableType tv)
>   | otherwise = checkType env p tvs (ConstructorType (qualify tv))
> checkType env p tvs (TupleType tys) =
>   liftA TupleType (mapA (checkType env p tvs) tys)
> checkType env p tvs (ListType ty) = liftA ListType (checkType env p tvs ty)
> checkType env p tvs (ArrowType ty1 ty2) =
>   liftA2 ArrowType (checkType env p tvs ty1) (checkType env p tvs ty2)
> checkType env p tvs (ApplyType ty1 ty2) =
>   liftA2 ApplyType (checkType env p tvs ty1) (checkType env p tvs ty2)

> checkClass :: TypeEnv -> Position -> [Ident] -> QualIdent -> Error ()
> checkClass env p tvs cls
>   | cls `elem` map qualify tvs = errorAt p (undefinedClass cls)
>   | otherwise =
>       case qualLookupTopEnv cls env of
>         [] -> errorAt p (undefinedClass cls)
>         [Data _ _] -> errorAt p (undefinedClass cls)
>         [Alias _] -> errorAt p (undefinedClass cls)
>         [Class _ _] -> return ()
>         _ -> internalError "checkClass"

> checkHiding :: Bool -> Position -> QualIdent -> [Ident] -> [Ident] -> Error ()
> checkHiding isType p tc xs xs' =
>   mapA_ (errorAt p . noElement isType tc) (nub (filter (`notElem` xs) xs'))

\end{verbatim}
\ToDo{Much of the above code could be shared with module
  \texttt{TypeSyntaxCheck}.}

Auxiliary functions.
\begin{verbatim}

> isTypeSynonym :: TypeEnv -> QualIdent -> Bool
> isTypeSynonym env tc =
>   case qualLookupTopEnv tc env of
>     [] | isPrimTypeId (unqualify tc) -> False
>     [Data _ _] -> False
>     [Alias _] -> True
>     _ -> internalError "isTypeSynonym"

\end{verbatim}
Error messages.
\begin{verbatim}

> undefinedType :: QualIdent -> String
> undefinedType tc = "Undefined type " ++ qualName tc

> undefinedClass :: QualIdent -> String
> undefinedClass cls = "Undefined type class " ++ qualName cls

> multipleArity :: Ident -> String
> multipleArity f =
>   "Method " ++ name f ++ " occurs more than once in ARITY pragma"

> nonLinear :: Ident -> String
> nonLinear tv =
>   "Type variable " ++ name tv ++
>   " occurs more than once on left hand side of type declaration"

> noElement :: Bool -> QualIdent -> Ident -> String
> noElement True tc x =
>   "Hidden constructor or label " ++ name x ++ " is not defined for type " ++
>   qualName tc
> noElement False cls f =
>   "Hidden method " ++ name f ++ " is not defined for class " ++ qualName cls

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

> arityTooBig :: Integer -> String
> arityTooBig n = "Function arity out of range: " ++ show n

\end{verbatim}
