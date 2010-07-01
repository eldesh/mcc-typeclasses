% -*- LaTeX -*-
% $Id: Desugar.lhs 2970 2010-07-01 09:11:20Z wlux $
%
% Copyright (c) 2001-2010, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Desugar.lhs}
\section{Desugaring Curry Expressions}\label{sec:desugar}
The desugaring pass removes most syntactic sugar from the module. In
particular, the output of the desugarer will have the following
properties.
\begin{itemize}
\item Patterns in equations and (f)case alternatives are composed of only
  \begin{itemize}
  \item literals,
  \item variables,
  \item constructor applications,
  \item function applications (function patterns),
  \item record patterns,
  \item as-patterns, and
  \item lazy patterns.
  \end{itemize}
\item Expressions are composed of only
  \begin{itemize}
  \item literals,
  \item variables,
  \item constructors,
  \item record constructions and updates,
  \item (binary) applications,
  \item lambda abstractions,
  \item let expressions, and
  \item (f)case expressions.
  \end{itemize}
\end{itemize}
Note that some syntactic sugar remains. In particular, we do not
replace boolean guards by if-then-else cascades and we do not
transform where clauses into let expressions. Both will happen only
after flattening patterns in case expressions, as this allows us to
handle the fall through behavior of boolean guards in case expressions
without introducing a special pattern match failure primitive (see
Sect.~\ref{sec:flatcase}). We also do not desugar lazy patterns and
the record syntax here. These are taken care of by ensuing compiler
phases.

\textbf{As we are going to insert references to real Prelude entities,
all names must be properly qualified before calling this module.}
\begin{verbatim}

> module Desugar(desugar) where
> import Base
> import Combined
> import Curry
> import CurryUtils
> import List
> import Monad
> import PredefIdent
> import PredefTypes
> import Ratio
> import Types
> import Typing

\end{verbatim}
New identifiers may be introduced while desugaring list
comprehensions. As usual, we use a state monad transformer for
generating unique names.
\begin{verbatim}

> type DesugarState a = StateT Int Id a

\end{verbatim}
The desugaring phase keeps only the type, function, and value
declarations of the module. At the top-level of a module, we just
desugar data constructor and type class and instance method
declarations. The top-level function declarations are treated like a
global declaration group.
\begin{verbatim}

> desugar :: Module QualType -> Module QualType
> desugar (Module m es is ds) = Module m es is (runSt (desugarModule ds) 1)

> desugarModule :: [TopDecl QualType] -> DesugarState [TopDecl QualType]
> desugarModule ds =
>   do
>     tds' <- mapM desugarTopDecl tds
>     vds' <- desugarDeclGroup [d | BlockDecl d <- vds]
>     return (tds' ++ map BlockDecl vds')
>   where (vds,tds) = partition isBlockDecl ds

> desugarTopDecl :: TopDecl QualType -> DesugarState (TopDecl QualType)
> desugarTopDecl (DataDecl p cx tc tvs cs clss) =
>   return (DataDecl p cx tc tvs (map desugarConstrDecl cs) clss)
>   where desugarConstrDecl (ConstrDecl p evs cx c tys) =
>           ConstrDecl p evs cx c tys
>         desugarConstrDecl (ConOpDecl p evs cx ty1 op ty2) =
>           ConstrDecl p evs cx op [ty1,ty2]
>         desugarConstrDecl (RecordDecl p evs cx c fs) =
>           RecordDecl p evs cx c fs
> desugarTopDecl (NewtypeDecl p cx tc tvs nc clss) =
>   return (NewtypeDecl p cx tc tvs nc clss)
> desugarTopDecl (TypeDecl p tc tvs ty) = return (TypeDecl p tc tvs ty)
> desugarTopDecl (ClassDecl p cx cls tv ds) =
>   liftM (ClassDecl p cx cls tv . (tds ++)) (desugarDeclGroup vds)
>   where (tds,vds) = partition isTypeSig ds
> desugarTopDecl (InstanceDecl p cx cls ty ds) =
>   liftM (InstanceDecl p cx cls ty) (desugarDeclGroup ds)
> desugarTopDecl (DefaultDecl p tys) = return (DefaultDecl p tys)
> --desugarTopDecl (BlockDecl d) = return (BlockDecl d)
> desugarTopDecl (SplitAnnot p) = return (SplitAnnot p)

\end{verbatim}
Within a declaration group, all fixity declarations, type signatures,
and trust annotations are discarded. The import entity specification
of foreign function declarations using the \texttt{ccall} and
\texttt{rawcall} calling conventions is expanded to always include the
kind of the declaration (either \texttt{static} or \texttt{dynamic})
and the name of the imported function.
\begin{verbatim}

> desugarDeclGroup :: [Decl QualType] -> DesugarState [Decl QualType]
> desugarDeclGroup ds = mapM desugarDecl (filter isValueDecl ds)

> desugarDecl :: Decl QualType -> DesugarState (Decl QualType)
> desugarDecl (FunctionDecl p ty f eqs) =
>   liftM (FunctionDecl p ty f) (mapM desugarEquation eqs)
> desugarDecl (ForeignDecl p (cc,s,ie) ty f ty') =
>   return (ForeignDecl p (cc,s `mplus` Just Safe,desugarImpEnt cc ie) ty f ty')
>   where desugarImpEnt cc ie
>           | cc == CallConvPrimitive = ie `mplus` Just (name f)
>           | otherwise = Just (unwords (kind (maybe [] words ie)))
>         kind [] = "static" : ident []
>         kind (x:xs)
>           | x == "static" = x : ident xs
>           | x == "dynamic" = [x]
>           | otherwise = "static" : ident (x:xs)
>         ident [] = [name f]
>         ident [x]
>           | x == "&" || ".h" `isSuffixOf` x = [x,name f]
>           | otherwise = [x]
>         ident [h,x]
>           | x == "&" = [h,x,name f]
>           | otherwise = [h,x]
>         ident [h,amp,f] = [h,amp,f]
>         ident _ = internalError "desugarImpEnt"
> desugarDecl (PatternDecl p t rhs) =
>   liftM2 (PatternDecl p) (desugarTerm t) (desugarRhs rhs)
> desugarDecl (FreeDecl p vs) = return (FreeDecl p vs)

> desugarEquation :: Equation QualType -> DesugarState (Equation QualType)
> desugarEquation (Equation p lhs rhs) =
>   liftM2 (Equation p . FunLhs f) (mapM desugarTerm ts) (desugarRhs rhs)
>   where (f,ts) = flatLhs lhs

\end{verbatim}
We expand each string literal in a pattern or expression into a list
of characters.
\begin{verbatim}

> desugarLiteralTerm :: QualType -> Literal
>                    -> Either (ConstrTerm QualType) (ConstrTerm QualType)
> desugarLiteralTerm ty (Char c) = Right (LiteralPattern ty (Char c))
> desugarLiteralTerm ty (Integer i) =
>   Right (LiteralPattern ty (fixLiteral (unqualType ty) i))
>   where fixLiteral (TypeConstrained tys _) = fixLiteral (head tys)
>         fixLiteral ty
>           | ty == floatType = Rational . toRational
>           | otherwise = Integer
> desugarLiteralTerm ty (Rational r) = Right (LiteralPattern ty (Rational r))
> desugarLiteralTerm ty (String cs) =
>   Left (ListPattern ty (map (LiteralPattern ty' . Char) cs))
>   where ty' = qualType (elemType (unqualType ty))

> desugarTerm :: ConstrTerm QualType -> DesugarState (ConstrTerm QualType)
> desugarTerm (LiteralPattern ty l) =
>   either desugarTerm return (desugarLiteralTerm ty l)
> desugarTerm (NegativePattern ty l) =
>   desugarTerm (LiteralPattern ty (negateLiteral l))
>   where negateLiteral (Integer i) = Integer (-i)
>         negateLiteral (Rational r) = Rational (-r)
>         negateLiteral _ = internalError "negateLiteral"
> desugarTerm (VariablePattern ty v) = return (VariablePattern ty v)
> desugarTerm (ConstructorPattern ty c ts) =
>   liftM (ConstructorPattern ty c) (mapM desugarTerm ts)
> desugarTerm (FunctionPattern ty f ts) =
>   liftM (FunctionPattern ty f) (mapM desugarTerm ts)
> desugarTerm (InfixPattern ty t1 op t2) = desugarTerm (desugarOp ty op [t1,t2])
>   where desugarOp ty (InfixConstr _ op) = ConstructorPattern ty op
>         desugarOp ty (InfixOp _ op) = FunctionPattern ty op
> desugarTerm (ParenPattern t) = desugarTerm t
> desugarTerm (RecordPattern ty c fs) =
>   liftM (RecordPattern ty c) (mapM (desugarField desugarTerm) fs)
> desugarTerm (TuplePattern ts) =
>   desugarTerm (ConstructorPattern ty (qTupleId (length ts)) ts)
>   where ty = qualType (tupleType (map typeOf ts))
> desugarTerm (ListPattern ty ts) = liftM (foldr cons nil) (mapM desugarTerm ts)
>   where nil = ConstructorPattern ty qNilId []
>         cons t ts = ConstructorPattern ty qConsId [t,ts]
> desugarTerm (AsPattern v t) = liftM (AsPattern v) (desugarTerm t)
> desugarTerm (LazyPattern t) = liftM LazyPattern (desugarTerm t)

\end{verbatim}
Anonymous identifiers in expressions are replaced by an expression
\texttt{let x free in x} where \texttt{x} is a fresh variable.
However, we must be careful with this transformation because the
compiler uses an anonymous identifier also for the name of the
program's initial goal (cf.\ Sect.~\ref{sec:goals}). This variable
must remain a free variable of the goal expression and therefore must
not be replaced.
\begin{verbatim}

> desugarRhs :: Rhs QualType -> DesugarState (Rhs QualType)
> desugarRhs (SimpleRhs p e ds) =
>   do
>     ds' <- desugarDeclGroup ds
>     e' <- desugarExpr p e
>     return (SimpleRhs p e' ds')
> desugarRhs (GuardedRhs es ds) =
>   do
>     ds' <- desugarDeclGroup ds
>     es' <- mapM desugarCondExpr es
>     return (GuardedRhs es' ds')

> desugarCondExpr :: CondExpr QualType -> DesugarState (CondExpr QualType)
> desugarCondExpr (CondExpr p g e) =
>   liftM2 (CondExpr p) (desugarExpr p g) (desugarExpr p e)

> desugarLiteral :: QualType -> Literal
>                -> Either (Expression QualType) (Expression QualType)
> desugarLiteral ty (Char c) = Right (Literal ty (Char c))
> desugarLiteral ty (Integer i) = Right (fixLiteral (unqualType ty) i)
>   where fixLiteral (TypeConstrained tys _) = fixLiteral (head tys)
>         fixLiteral ty'
>           | ty' `elem` [intType,integerType] = Literal ty . Integer
>           | ty' == floatType = Literal ty . Rational . fromInteger
>           | ty' == rationalType = desugarRatio . fromInteger
>           | otherwise =
>               Apply (prelFromInteger (unqualType ty)) .
>               Literal qualIntegerType . Integer
> desugarLiteral ty (Rational r) = Right (fixLiteral (unqualType ty) r)
>   where fixLiteral (TypeConstrained tys _) = fixLiteral (head tys)
>         fixLiteral ty'
>           | ty' == floatType = Literal ty . Rational
>           | ty' == rationalType = desugarRatio
>           | otherwise =
>               Apply (prelFromRational (unqualType ty)) . desugarRatio
> desugarLiteral ty (String cs) = Left (List ty (map (Literal ty' . Char) cs))
>   where ty' = qualType (elemType (unqualType ty))

> desugarRatio :: Rational -> Expression QualType
> desugarRatio r =
>   foldl applyToInteger (ratioConstr integerType) [numerator r,denominator r]
>   where applyToInteger e = Apply e . Literal qualIntegerType . Integer

> desugarExpr :: Position -> Expression QualType
>             -> DesugarState (Expression QualType)
> desugarExpr p (Literal ty l) =
>   either (desugarExpr p) return (desugarLiteral ty l)
> desugarExpr p (Variable ty v)
>   -- NB The name of the initial goal is anonId (not renamed, cf. goalModule
>   --    in module Goals) and must not be changed
>   | isRenamed v' && unRenameIdent v' == anonId =
>       do
>         v'' <- freshVar "_#var" (unqualType ty)
>         return (Let [FreeDecl p [uncurry FreeVar v'']] (uncurry mkVar v''))
>   | otherwise = return (Variable ty v)
>   where v' = unqualify v
> desugarExpr _ (Constructor ty c) = return (Constructor ty c)
> desugarExpr p (Paren e) = desugarExpr p e
> desugarExpr p (Typed e _) = desugarExpr p e
> desugarExpr p (Record ty c fs) =
>   liftM (Record ty c) (mapM (desugarField (desugarExpr p)) fs)
> desugarExpr p (RecordUpdate e fs) =
>   liftM2 RecordUpdate
>          (desugarExpr p e)
>          (mapM (desugarField (desugarExpr p)) fs)
> desugarExpr p (Tuple es) =
>   liftM (apply (Constructor ty (qTupleId (length es))))
>         (mapM (desugarExpr p) es)
>   where ty = qualType (foldr TypeArrow (tupleType tys) tys)
>         tys = map typeOf es
> desugarExpr p (List ty es) = liftM (foldr cons nil) (mapM (desugarExpr p) es)
>   where nil = Constructor ty qNilId
>         cons = Apply . Apply (Constructor ty' qConsId)
>         ty' = qualType (consType (elemType (unqualType ty)))
> desugarExpr p (ListCompr e qs) = desugarListCompr e qs z >>= desugarExpr p
>   where z = List (qualType (typeOf (ListCompr e qs))) []
> desugarExpr p (EnumFrom e) =
>   liftM (Apply (prelEnumFrom (typeOf e))) (desugarExpr p e)
> desugarExpr p (EnumFromThen e1 e2) =
>   liftM (apply (prelEnumFromThen (typeOf e1))) (mapM (desugarExpr p) [e1,e2])
> desugarExpr p (EnumFromTo e1 e2) =
>   liftM (apply (prelEnumFromTo (typeOf e1))) (mapM (desugarExpr p) [e1,e2])
> desugarExpr p (EnumFromThenTo e1 e2 e3) =
>   liftM (apply (prelEnumFromThenTo (typeOf e1)))
>         (mapM (desugarExpr p) [e1,e2,e3])
> desugarExpr p (UnaryMinus e) =
>   liftM (Apply (prelNegate (typeOf e))) (desugarExpr p e)
> desugarExpr p (Apply e1 e2) =
>   liftM2 Apply (desugarExpr p e1) (desugarExpr p e2)
> desugarExpr p (InfixApply e1 op e2) =
>   do
>     op' <- desugarExpr p (infixOp op)
>     e1' <- desugarExpr p e1
>     e2' <- desugarExpr p e2
>     return (Apply (Apply op' e1') e2')
> desugarExpr p (LeftSection e op) =
>   do
>     op' <- desugarExpr p (infixOp op)
>     e' <- desugarExpr p e
>     return (Apply op' e')
> desugarExpr p (RightSection op e) =
>   do
>     op' <- desugarExpr p (infixOp op)
>     e' <- desugarExpr p e
>     return (Apply (Apply (prelFlip ty1 ty2 ty3) op') e')
>   where TypeArrow ty1 (TypeArrow ty2 ty3) = typeOf (infixOp op)
> desugarExpr _ (Lambda p ts e) =
>   liftM2 (Lambda p) (mapM desugarTerm ts) (desugarExpr p e)
> desugarExpr p (Let ds e) = liftM2 Let (desugarDeclGroup ds) (desugarExpr p e)
> desugarExpr p (Do sts e) = desugarExpr p (foldr desugarStmt e sts)
>   where desugarStmt (StmtExpr e) e' =
>           apply (prelBind_ (typeOf e) (typeOf e')) [e,e']
>         desugarStmt (StmtBind p t e) e' =
>           apply (prelBind (typeOf e) (typeOf t) (typeOf e'))
>                 [e,Lambda p [t] e']
>         desugarStmt (StmtDecl ds) e' = mkLet ds e'
> desugarExpr p (IfThenElse e1 e2 e3) =
>   liftM3 mkCase (desugarExpr p e1) (desugarExpr p e2) (desugarExpr p e3)
>   where mkCase e1 e2 e3 =
>           Case e1 [caseAlt p truePattern e2,caseAlt p falsePattern e3]
> desugarExpr p (Case e as) = liftM2 Case (desugarExpr p e) (mapM desugarAlt as)
> desugarExpr p (Fcase e as) =
>   liftM2 Fcase (desugarExpr p e) (mapM desugarAlt as)

> desugarAlt :: Alt QualType -> DesugarState (Alt QualType)
> desugarAlt (Alt p t rhs) = liftM2 (Alt p) (desugarTerm t) (desugarRhs rhs)

> desugarField :: (a -> DesugarState a) -> Field a -> DesugarState (Field a)
> desugarField desugar (Field l e) = liftM (Field l) (desugar e)

\end{verbatim}
List comprehensions are desugared with the following optimized
translation scheme, which constructs the denoted list with (nested)
foldr applications.
\begin{displaymath}
  \newcommand{\semant}[2]{\mathcal{#1}[\![#2]\!]}
  \renewcommand{\arraystretch}{1.2}
  \begin{array}{r@{\;}c@{\;}l}
    \semant{D}{\texttt{[$e$|$qs$]}} &=&
      \semant{L}{\texttt{[$e$|$qs$]}}(\texttt{[]}) \\
    \semant{L}{\texttt{[$e$|]}}(z) &=& \texttt{$e$:$z$} \\
    \semant{L}{\texttt{[$e$|$b$,$qs$]}}(z) &=&
      \texttt{if $b$ then $\semant{L}{\texttt{[$e$|$qs$]}}(z)$ else $z$} \\
    \semant{L}{\texttt{[$e$|$t$<-$l$,$qs$]}}(z) &=& \\
    \texttt{foldr} & \multicolumn{2}{l}{\texttt{(\char`\\$x$ $y$ -> case $x$ of \char`\{\
          $t$ -> $\semant{L}{\texttt{[$e$|$qs$]}}(y)$; \_ -> $y$ \char`\}) $z$ $l$}}\\
     \textrm{where} & \multicolumn{2}{@{}l}{\textrm{$x$, $y$ are fresh identifiers}} \\
    \semant{L}{\texttt{[$e$|let $ds$,$qs$]}}(z) &=&
      \texttt{let $ds$ in $\semant{L}{\texttt{[$e$|$qs$]}}(z)$} \\
  \end{array}
\end{displaymath}
Note that the transformation scheme uses a rigid case expression to
match the pattern of a \texttt{$t$<-$l$} qualifier, which differs from
the Curry report (cf.\ Sect.~5.2 in~\cite{Hanus:Report}). We use a
rigid match here because it makes the translation scheme simpler,
since we do not need to compute the set of patterns that are
incompatible with $t$ and we do not need a special case for literal
patterns. In addition, it looks dubious to have list comprehension
qualifiers generate fresh instances of $t$ that do not contribute to
the list at all.
\begin{verbatim}

> desugarListCompr :: Expression QualType -> [Statement QualType]
>                  -> Expression QualType -> DesugarState (Expression QualType)
> desugarListCompr e [] z =
>   return (apply (Constructor (qualType (consType (typeOf e))) qConsId) [e,z])
> desugarListCompr e (q:qs) z =
>   desugarQual q z >>= \(y,f) -> desugarListCompr e qs y >>= return . f

> desugarQual :: Statement QualType -> Expression QualType
>             -> DesugarState (Expression QualType,
>                              Expression QualType -> Expression QualType)
> desugarQual (StmtExpr b) z = return (z,\e -> IfThenElse b e z)
> desugarQual (StmtBind p t l) z =
>   do
>     v <- freshVar "_#var" (typeOf t)
>     y <- freshVar "_#var" (typeOf z)
>     return (uncurry mkVar y,
>             \e -> apply (prelFoldr (unqualType (fst v)) (unqualType (fst y)))
>                         [foldFunct v y e,z,l])
>   where foldFunct v l e =
>           Lambda p [uncurry VariablePattern v,uncurry VariablePattern l]
>             (Case (uncurry mkVar v)
>                   [caseAlt p t e,
>                    caseAlt p (uncurry VariablePattern v) (uncurry mkVar l)])
> desugarQual (StmtDecl ds) z = return (z,Let ds)

\end{verbatim}
Generation of fresh names.
\begin{verbatim}

> freshVar :: String -> Type -> DesugarState (QualType,Ident)
> freshVar prefix ty =
>   do
>     v <- liftM (mkName prefix) (updateSt (1 +))
>     return (qualType ty,v)
>   where mkName pre n = mkIdent (pre ++ show n)

\end{verbatim}
Prelude entities.
\begin{verbatim}

> prelFromInteger a = preludeFun [integerType] a "fromInteger"
> prelFromRational a = preludeFun [rationalType] a "fromRational"
> prelBind ma a mb = preludeFun [ma,a `TypeArrow` mb] mb ">>="
> prelBind_ ma mb = preludeFun [ma,mb] mb ">>"
> prelFlip a b c = preludeFun [a `TypeArrow` (b `TypeArrow` c),b,a] c "flip"
> prelEnumFrom a = preludeFun [a] (listType a) "enumFrom"
> prelEnumFromTo a = preludeFun [a,a] (listType a) "enumFromTo"
> prelEnumFromThen a = preludeFun [a,a] (listType a) "enumFromThen"
> prelEnumFromThenTo a = preludeFun [a,a,a] (listType a) "enumFromThenTo"
> prelFoldr a b =
>   preludeFun [a `TypeArrow` (b `TypeArrow` b),b,listType a] b "foldr"
> prelNegate a = preludeFun [a] a "negate"

> preludeFun :: [Type] -> Type -> String -> Expression QualType
> preludeFun tys ty f =
>   Variable (qualType (foldr TypeArrow ty tys))
>            (qualifyWith preludeMIdent (mkIdent f))

> ratioConstr :: Type -> Expression QualType
> ratioConstr ty =
>   Constructor (qualType (TypeArrow ty (TypeArrow ty (ratioType ty))))
>               (qualifyWith ratioMIdent (mkIdent ":%"))

> truePattern, falsePattern :: ConstrTerm QualType
> truePattern = ConstructorPattern qualBoolType qTrueId []
> falsePattern = ConstructorPattern qualBoolType qFalseId []

\end{verbatim}
Auxiliary definitions.
\begin{verbatim}

> consType :: Type -> Type
> consType a = TypeArrow a (TypeArrow (listType a) (listType a))

> elemType :: Type -> Type
> elemType (TypeApply (TypeConstructor tc) ty) | tc == qListId = ty
> elemType ty = internalError ("elemType " ++ show ty)

\end{verbatim}
