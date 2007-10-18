% -*- LaTeX -*-
% $Id: IntfEquiv.lhs 2513 2007-10-18 09:50:08Z wlux $
%
% Copyright (c) 2000-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{IntfEquiv.lhs}
\section{Comparing Module Interfaces}
If a module is recompiled, the compiler has to check whether the
interface file must be updated. This must be done if any exported
entity has been changed, or an export was removed or added. The
function \texttt{intfEquiv} checks whether two interfaces are
equivalent, i.e., whether they define the same entities.

\textbf{Note:} There is deliberately no list instance for
\texttt{IntfEquiv} because the order of interface declarations is
irrelevant, whereas it is decisive for the constructor declarations
of a data type. By not providing a list instance, we cannot
inadvertently mix up these cases.
\begin{verbatim}

> module IntfEquiv(fixInterface, intfEquiv) where
> import Curry
> import List
> import Set

> infix 4 =~=, `eqvList`, `eqvSet`

> intfEquiv :: Interface -> Interface -> Bool
> intfEquiv = (=~=)

> class IntfEquiv a where
>   (=~=) :: a -> a -> Bool

> eqvList, eqvSet :: IntfEquiv a => [a] -> [a] -> Bool
> xs `eqvList` ys = length xs == length ys && and (zipWith (=~=) xs ys)
> xs `eqvSet` ys =
>   null (deleteFirstsBy (=~=) xs ys ++ deleteFirstsBy (=~=) ys xs)

> instance IntfEquiv a => IntfEquiv (Maybe a) where
>   Nothing =~= Nothing = True
>   Nothing =~= Just _  = False
>   Just _  =~= Nothing = False
>   Just x  =~= Just y  = x =~= y

> instance IntfEquiv Interface where
>   Interface m1 is1 ds1 =~= Interface m2 is2 ds2 =
>     m1 == m2 && is1 `eqvSet` is2 && ds1 `eqvSet` ds2

> instance IntfEquiv IImportDecl where
>   IImportDecl _ m1 =~= IImportDecl _ m2 = m1 == m2

> instance IntfEquiv IDecl where
>   IInfixDecl _ fix1 p1 op1 =~= IInfixDecl _ fix2 p2 op2 =
>     fix1 == fix2 && p1 == p2 && op1 == op2
>   HidingDataDecl _ tc1 k1 tvs1 =~= HidingDataDecl _ tc2 k2 tvs2 =
>     tc1 == tc2 && k1 == k2 && tvs1 == tvs2
>   IDataDecl _ cx1 tc1 k1 tvs1 cs1 =~= IDataDecl _ cx2 tc2 k2 tvs2 cs2 =
>     cx1 == cx2 && tc1 == tc2 && k1 == k2 && tvs1 == tvs2 && cs1 `eqvList` cs2
>   INewtypeDecl _ cx1 tc1 k1 tvs1 nc1 =~= INewtypeDecl _ cx2 tc2 k2 tvs2 nc2 =
>     cx1 == cx2 && tc1 == tc2 && k1 == k2 && tvs1 == tvs2 && nc1 =~= nc2
>   ITypeDecl _ tc1 k1 tvs1 ty1 =~= ITypeDecl _ tc2 k2 tvs2 ty2 =
>     tc1 == tc2 && k1 == k2 && tvs1 == tvs2 && ty1 == ty2
>   HidingClassDecl _ cx1 cls1 k1 _ =~= HidingClassDecl _ cx2 cls2 k2 _ =
>     cx1 == cx2 && cls1 == cls2 && k1 == k2
>   IClassDecl _ cx1 cls1 k1 _ ds1 =~= IClassDecl _ cx2 cls2 k2 _ ds2 =
>     cx1 == cx2 && cls1 == cls2 && k1 == k2 && ds1 `eqvList` ds2
>   IInstanceDecl _ cx1 cls1 ty1 m1 =~= IInstanceDecl _ cx2 cls2 ty2 m2 =
>     cx1 == cx2 && cls1 == cls2 && ty1 == ty2 && m1 == m2
>   IFunctionDecl _ f1 n1 ty1 =~= IFunctionDecl _ f2 n2 ty2 =
>     f1 == f2 && n1 == n2 && ty1 == ty2
>   _ =~= _ = False

> instance IntfEquiv ConstrDecl where
>   ConstrDecl _ evs1 cx1 c1 tys1 =~= ConstrDecl _ evs2 cx2 c2 tys2 =
>     c1 == c2 && evs1 == evs2 && cx1 == cx2 && tys1 == tys2
>   ConOpDecl _ evs1 cx1 ty11 op1 ty12 =~= ConOpDecl _ evs2 cx2 ty21 op2 ty22 =
>     op1 == op2 && evs1 == evs2 && cx1 == cx2 && ty11 == ty21 && ty12 == ty22
>   _ =~= _ = False

> instance IntfEquiv NewConstrDecl where
>   NewConstrDecl _ c1 ty1 =~= NewConstrDecl _ c2 ty2 = c1 == c2 && ty1 == ty2

> instance IntfEquiv IMethodDecl where
>   IMethodDecl _ f1 ty1 =~= IMethodDecl _ f2 ty2 = f1 == f2 && ty1 == ty2

\end{verbatim}
If we check for a change in the interface, we do not need to check the
interface declarations, but still must disambiguate (nullary) type
constructors and type variables in type expressions. This is handled
by function \texttt{fixInterface} and the associated type class
\texttt{FixInterface}.
\begin{verbatim}

> fixInterface :: Interface -> Interface
> fixInterface (Interface m is ds) =
>   Interface m is (fix (fromListSet (typeConstructors ds)) ds)

> class FixInterface a where
>   fix :: Set Ident -> a -> a

> instance FixInterface a => FixInterface (Maybe a) where
>   fix tcs = fmap (fix tcs)

> instance FixInterface a => FixInterface [a] where
>   fix tcs = map (fix tcs)

> instance FixInterface IDecl where
>   fix _ (IInfixDecl p fix pr op) = IInfixDecl p fix pr op
>   fix _ (HidingDataDecl p tc k tvs) = HidingDataDecl p tc k tvs
>   fix tcs (IDataDecl p cx tc k tvs cs) =
>     IDataDecl p (fix tcs cx) tc k tvs (fix tcs cs)
>   fix tcs (INewtypeDecl p cx tc k tvs nc) =
>     INewtypeDecl p (fix tcs cx) tc k tvs (fix tcs nc)
>   fix tcs (ITypeDecl p tc k tvs ty) = ITypeDecl p tc k tvs (fix tcs ty)
>   fix tcs (HidingClassDecl p cx cls k tv) =
>     HidingClassDecl p (fix tcs cx) cls k tv
>   fix tcs (IClassDecl p cx cls k tv ds) =
>     IClassDecl p (fix tcs cx) cls k tv (fix tcs ds)
>   fix tcs (IInstanceDecl p cx cls ty m) =
>     IInstanceDecl p (fix tcs cx) cls (fix tcs ty) m
>   fix tcs (IFunctionDecl p f n ty) = IFunctionDecl p f n (fix tcs ty)

> instance FixInterface ConstrDecl where
>   fix tcs (ConstrDecl p evs cx c tys) = ConstrDecl p evs cx c (fix tcs tys)
>   fix tcs (ConOpDecl p evs cx ty1 op ty2) =
>     ConOpDecl p evs cx (fix tcs ty1) op (fix tcs ty2)

> instance FixInterface NewConstrDecl where
>   fix tcs (NewConstrDecl p c ty) = NewConstrDecl p c (fix tcs ty)

> instance FixInterface IMethodDecl where
>   fix tcs (IMethodDecl p f ty) = IMethodDecl p f (fix tcs ty)

> instance FixInterface QualTypeExpr where
>   fix tcs (QualTypeExpr cx ty) = QualTypeExpr (fix tcs cx) (fix tcs ty)

> instance FixInterface ClassAssert where
>   fix tcs (ClassAssert cls ty) = ClassAssert cls (fix tcs ty)

> instance FixInterface TypeExpr where
>   fix tcs (ConstructorType tc)
>     | isQualified tc || isPrimTypeId tc || tc' `elemSet` tcs =
>         ConstructorType tc
>     | otherwise = VariableType tc'
>     where tc' = unqualify tc
>   fix tcs (VariableType tv)
>     | tv `elemSet` tcs = ConstructorType (qualify tv)
>     | otherwise = VariableType tv
>   fix tcs (TupleType tys) = TupleType (fix tcs tys)
>   fix tcs (ListType ty) = ListType (fix tcs ty)
>   fix tcs (ArrowType ty1 ty2) = ArrowType (fix tcs ty1) (fix tcs ty2)
>   fix tcs (ApplyType ty1 ty2) = ApplyType (fix tcs ty1) (fix tcs ty2)

> typeConstructors :: [IDecl] -> [Ident]
> typeConstructors ds =
>   [tc | (Nothing,tc) <- map splitQualIdent (foldr tcs [] ds)]
>   where tcs (IInfixDecl _ _ _ _) tcs = tcs
>         tcs (HidingDataDecl _ tc _ _) tcs = tc : tcs
>         tcs (IDataDecl _ _ tc _ _ _) tcs = tc : tcs
>         tcs (INewtypeDecl _ _ tc _ _ _) tcs = tc : tcs
>         tcs (ITypeDecl _ tc _ _ _) tcs = tc : tcs
>         tcs (HidingClassDecl _ _ _ _ _) tcs = tcs
>         tcs (IClassDecl _ _ _ _ _ _) tcs = tcs
>         tcs (IInstanceDecl _ _ _ _ _) tcs = tcs
>         tcs (IFunctionDecl _ _ _ _) tcs = tcs

\end{verbatim}
