% -*- LaTeX -*-
% $Id: IntfQual.lhs 2815 2009-05-04 13:59:57Z wlux $
%
% Copyright (c) 2008, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{IntfQual.lhs}
\section{Qualification of Interface Declarations}
After applying syntax checking to an interface, the compiler properly
qualifies all unqualified identifiers in the interface in order to
simplify processing. On the other hand, the names of entities defined
in the current module are changed back into unqualified identifiers in
the final interface of the current module in order to improve
readability.

\ToDo{In order to improve readability further, remove module
  qualifiers in the right hand side of interface declarations for all
  names which are unambiguous.}
\begin{verbatim}

> module IntfQual(Qual, qualIntf,unqualIntf) where
> import Base
> import Curry
> import IdentInfo
> import PredefIdent

> qualIntf :: Qual a => ModuleIdent -> a -> a
> qualIntf = mapQId qualQualify

> unqualIntf :: Qual a => ModuleIdent -> a -> a
> unqualIntf = mapQId qualUnqualify

> class Qual a where
>   mapQId :: (ModuleIdent -> QualIdent -> QualIdent) -> ModuleIdent -> a -> a

> instance Qual a => Qual [a] where
>   mapQId q m = map (mapQId q m)

> instance Qual IDecl where
>   mapQId q m (IInfixDecl p fix pr op) = IInfixDecl p fix pr (mapDC q m op)
>   mapQId q m (HidingDataDecl p tc k tvs) =
>     HidingDataDecl p (mapTC q m tc) k tvs
>   mapQId q m (IDataDecl p cx tc k tvs cs xs) =
>     IDataDecl p (mapQId q m cx) (mapTC q m tc) k tvs (mapQId q m cs) xs
>   mapQId q m (INewtypeDecl p cx tc k tvs nc xs) =
>     INewtypeDecl p (mapQId q m cx) (mapTC q m tc) k tvs (mapQId q m nc) xs
>   mapQId q m (ITypeDecl p tc k tvs ty) =
>     ITypeDecl p (mapTC q m tc) k tvs (mapQId q m ty)
>   mapQId q m (HidingClassDecl p cx cls k tv) =
>     HidingClassDecl p (mapQId q m cx) (q m cls) k tv
>   mapQId q m (IClassDecl p cx cls k tv fs fs') =
>     IClassDecl p (mapQId q m cx) (q m cls) k tv (mapQId q m fs) fs'
>   mapQId q m (IInstanceDecl p cx cls ty m' fs) =
>     IInstanceDecl p (mapQId q m cx) (q m cls) (mapQId q m ty) m'' fs
>     where m'' = fst $ splitQualIdent $ q m
>                     $ maybe qualify qualifyWith m' anonId
>   mapQId q m (IFunctionDecl p f n ty) =
>     IFunctionDecl p (q m f) n (mapQId q m ty)

> instance Qual ConstrDecl where
>   mapQId q m (ConstrDecl p tvs cx c tys) =
>     ConstrDecl p tvs (mapQId q m cx) c (mapQId q m tys)
>   mapQId q m (ConOpDecl p tvs cx ty1 op ty2) =
>     ConOpDecl p tvs (mapQId q m cx) (mapQId q m ty1) op (mapQId q m ty2)
>   mapQId q m (RecordDecl p tvs cx c fs) =
>     RecordDecl p tvs (mapQId q m cx) c (mapQId q m fs)

> instance Qual NewConstrDecl where
>   mapQId q m (NewConstrDecl p c ty) = NewConstrDecl p c (mapQId q m ty)
>   mapQId q m (NewRecordDecl p c l ty) = NewRecordDecl p c l (mapQId q m ty)

> instance Qual FieldDecl where
>   mapQId q m (FieldDecl p ls ty) = FieldDecl p ls (mapQId q m ty)

> instance Qual IMethodDecl where
>   mapQId q m (IMethodDecl p f n ty) = IMethodDecl p f n (mapQId q m ty)

> instance Qual QualTypeExpr where
>   mapQId q m (QualTypeExpr cx ty) =
>     QualTypeExpr (mapQId q m cx) (mapQId q m ty)

> instance Qual ClassAssert where
>   mapQId q m (ClassAssert cls ty) = ClassAssert (q m cls) (mapQId q m ty)

> instance Qual TypeExpr where
>   mapQId q m (ConstructorType tc) = ConstructorType (mapTC q m tc)
>   mapQId q _ (VariableType tv) = VariableType tv
>   mapQId q m (TupleType tys) = TupleType (mapQId q m tys)
>   mapQId q m (ListType ty) = ListType (mapQId q m ty)
>   mapQId q m (ArrowType ty1 ty2) = ArrowType (mapQId q m ty1) (mapQId q m ty2)
>   mapQId q m (ApplyType ty1 ty2) = ApplyType (mapQId q m ty1) (mapQId q m ty2)

> mapTC, mapDC :: (ModuleIdent -> QualIdent -> QualIdent)
>              -> ModuleIdent -> QualIdent -> QualIdent
> mapTC = mapQIdent isPrimTypeId
> mapDC = mapQIdent isPrimDataId

> mapQIdent :: (Ident -> Bool) -> (ModuleIdent -> QualIdent -> QualIdent)
>           -> ModuleIdent -> QualIdent -> QualIdent
> mapQIdent p q m x = q (if p (unqualify x) then preludeMIdent else m) x

\end{verbatim}
