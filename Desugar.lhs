% -*- LaTeX -*-
% $Id: Desugar.lhs 2800 2009-04-26 16:54:22Z wlux $
%
% Copyright (c) 2001-2009, Wolfgang Lux
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
  \item let expressions,
  \item if-then-else expressions, and
  \item (f)case expressions.
  \end{itemize}
\end{itemize}
Note that some syntactic sugar remains. In particular, we do not
replace boolean guards by if-then-else cascades and we do not
transform where clauses into let expressions. Both will happen only
after flattening patterns in case expressions, as this allows us to
handle the fall through behavior of boolean guards in case expressions
without introducing a special pattern match failure primitive (see
Sect.~\ref{sec:flatcase}). We also do not desugar if-then-else
expressions, lazy patterns, and the record syntax here. The former is
taken care of by the case matching phase, too, and lazy patterns and
the records are desugared by ensuing compiler phases.

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
> import ValueInfo

\end{verbatim}
New identifiers may be introduced while desugaring list
comprehensions. As usual, we use a state monad transformer for
generating unique names. In addition, the state is also used for
passing through the type environment, which is augmented with the
types of the new variables.
\begin{verbatim}

> type DesugarState a = StateT ValueEnv (StateT Int Id) a

> run :: DesugarState a -> ValueEnv -> a
> run m tyEnv = runSt (callSt m tyEnv) 1

\end{verbatim}
The desugaring phase keeps only the type, function, and value
declarations of the module. At the top-level of a module, we just
desugar data constructor and type class and instance method
declarations. The top-level function declarations are treated like a
global declaration group.
\begin{verbatim}

> desugar :: ValueEnv -> Module Type -> (Module Type,ValueEnv)
> desugar tyEnv (Module m es is ds) = (Module m es is ds',tyEnv')
>   where (ds',tyEnv') = run (desugarModule m ds) tyEnv

> desugarModule :: ModuleIdent -> [TopDecl Type]
>               -> DesugarState ([TopDecl Type],ValueEnv)
> desugarModule m ds =
>   do
>     tds' <- mapM (desugarTopDecl m) tds
>     vds' <- desugarDeclGroup m [d | BlockDecl d <- vds]
>     tyEnv' <- fetchSt
>     return (tds' ++ map BlockDecl vds',tyEnv')
>   where (vds,tds) = partition isBlockDecl ds

> desugarTopDecl :: ModuleIdent -> TopDecl Type -> DesugarState (TopDecl Type)
> desugarTopDecl m (DataDecl p cx tc tvs cs clss) =
>   return (DataDecl p cx tc tvs (map desugarConstrDecl cs) clss)
>   where desugarConstrDecl (ConstrDecl p evs cx c tys) =
>           ConstrDecl p evs cx c tys
>         desugarConstrDecl (ConOpDecl p evs cx ty1 op ty2) =
>           ConstrDecl p evs cx op [ty1,ty2]
>         desugarConstrDecl (RecordDecl p evs cx c fs) =
>           RecordDecl p evs cx c fs
> desugarTopDecl m (NewtypeDecl p cx tc tvs nc clss) =
>   return (NewtypeDecl p cx tc tvs nc clss)
> desugarTopDecl _ (TypeDecl p tc tvs ty) = return (TypeDecl p tc tvs ty)
> desugarTopDecl m (ClassDecl p cx cls tv ds) =
>   liftM (ClassDecl p cx cls tv . (tds ++)) (desugarDeclGroup m vds)
>   where (tds,vds) = partition isTypeSig ds
> desugarTopDecl m (InstanceDecl p cx cls ty ds) =
>   liftM (InstanceDecl p cx cls ty) (desugarDeclGroup m ds)
> desugarTopDecl _ (DefaultDecl p tys) = return (DefaultDecl p tys)
> --desugarTopDecl _ (BlockDecl d) = return (BlockDecl d)
> desugarTopDecl _ (SplitAnnot p) = return (SplitAnnot p)

\end{verbatim}
Within a declaration group, all fixity declarations, type signatures,
and trust annotations are discarded. The import entity specification
of foreign function declarations using the \texttt{ccall} and
\texttt{rawcall} calling conventions is expanded to always include the
kind of the declaration (either \texttt{static} or \texttt{dynamic})
and the name of the imported function.
\begin{verbatim}

> desugarDeclGroup :: ModuleIdent -> [Decl Type] -> DesugarState [Decl Type]
> desugarDeclGroup m ds = mapM (desugarDecl m) (filter isValueDecl ds)

> desugarDecl :: ModuleIdent -> Decl Type -> DesugarState (Decl Type)
> desugarDecl m (FunctionDecl p f eqs) =
>   liftM (FunctionDecl p f) (mapM (desugarEquation m) eqs)
> desugarDecl _ (ForeignDecl p cc s ie f ty) =
>   return (ForeignDecl p cc (s `mplus` Just Safe) (desugarImpEnt cc ie) f ty)
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
> desugarDecl m (PatternDecl p t rhs) =
>   liftM2 (PatternDecl p) (desugarTerm m t) (desugarRhs m rhs)
> desugarDecl _ (FreeDecl p vs) = return (FreeDecl p vs)

> desugarEquation :: ModuleIdent -> Equation Type
>                 -> DesugarState (Equation Type)
> desugarEquation m (Equation p lhs rhs) =
>   liftM2 (Equation p . FunLhs f) (mapM (desugarTerm m) ts) (desugarRhs m rhs)
>   where (f,ts) = flatLhs lhs

\end{verbatim}
We expand each string literal in a pattern or expression into a list
of characters.
\begin{verbatim}

> desugarLiteralTerm :: Type -> Literal
>                    -> Either (ConstrTerm Type) (ConstrTerm Type)
> desugarLiteralTerm ty (Char c) = Right (LiteralPattern ty (Char c))
> desugarLiteralTerm ty (Integer i) =
>   Right (LiteralPattern ty (fixLiteral ty i))
>   where fixLiteral (TypeConstrained tys _) = fixLiteral (head tys)
>         fixLiteral ty
>           | ty == floatType = Rational . toRational
>           | otherwise = Integer
> desugarLiteralTerm ty (Rational r) = Right (LiteralPattern ty (Rational r))
> desugarLiteralTerm ty (String cs) =
>   Left (ListPattern ty (map (LiteralPattern (elemType ty) . Char) cs))

> desugarTerm :: ModuleIdent -> ConstrTerm Type
>             -> DesugarState (ConstrTerm Type)
> desugarTerm m (LiteralPattern ty l) =
>   either (desugarTerm m) return (desugarLiteralTerm ty l)
> desugarTerm m (NegativePattern ty l) =
>   desugarTerm m (LiteralPattern ty (negateLiteral l))
>   where negateLiteral (Integer i) = Integer (-i)
>         negateLiteral (Rational r) = Rational (-r)
>         negateLiteral _ = internalError "negateLiteral"
> desugarTerm _ (VariablePattern ty v) = return (VariablePattern ty v)
> desugarTerm m (ConstructorPattern ty c ts) =
>   liftM (ConstructorPattern ty c) (mapM (desugarTerm m) ts)
> desugarTerm m (InfixPattern ty t1 op t2) =
>   desugarTerm m (ConstructorPattern ty op [t1,t2])
> desugarTerm m (ParenPattern t) = desugarTerm m t
> desugarTerm m (RecordPattern ty c fs) =
>   liftM (RecordPattern ty c) (mapM (desugarField (desugarTerm m)) fs)
> desugarTerm m (TuplePattern ts) =
>   desugarTerm m (ConstructorPattern ty (qTupleId (length ts)) ts)
>   where ty = tupleType (map typeOf ts)
> desugarTerm m (ListPattern ty ts) =
>   liftM (foldr cons nil) (mapM (desugarTerm m) ts)
>   where nil = ConstructorPattern ty qNilId []
>         cons t ts = ConstructorPattern ty qConsId [t,ts]
> desugarTerm m (AsPattern v t) = liftM (AsPattern v) (desugarTerm m t)
> desugarTerm m (LazyPattern t) = liftM LazyPattern (desugarTerm m t)

\end{verbatim}
Anonymous identifiers in expressions are replaced by an expression
\texttt{let x free in x} where \texttt{x} is a fresh variable.
However, we must be careful with this transformation because the
compiler uses an anonymous identifier also for the name of the
program's initial goal (cf.\ Sect.~\ref{sec:goals}). This variable
must remain a free variable of the goal expression and therefore must
not be replaced.
\begin{verbatim}

> desugarRhs :: ModuleIdent -> Rhs Type -> DesugarState (Rhs Type)
> desugarRhs m (SimpleRhs p e ds) =
>   do
>     ds' <- desugarDeclGroup m ds
>     e' <- desugarExpr m p e
>     return (SimpleRhs p e' ds')
> desugarRhs m (GuardedRhs es ds) =
>   do
>     ds' <- desugarDeclGroup m ds
>     es' <- mapM (desugarCondExpr m) es
>     return (GuardedRhs es' ds')

> desugarCondExpr :: ModuleIdent -> CondExpr Type
>                 -> DesugarState (CondExpr Type)
> desugarCondExpr m (CondExpr p g e) =
>   liftM2 (CondExpr p) (desugarExpr m p g) (desugarExpr m p e)

> desugarLiteral :: Type -> Literal
>                -> Either (Expression Type) (Expression Type)
> desugarLiteral ty (Char c) = Right (Literal ty (Char c))
> desugarLiteral ty (Integer i) = Right (fixLiteral ty i)
>   where fixLiteral (TypeConstrained tys _) = fixLiteral (head tys)
>         fixLiteral ty'
>           | ty' `elem` [intType,integerType] = Literal ty . Integer
>           | ty' == floatType = Literal ty . Rational . fromInteger
>           | ty' == rationalType = desugarRatio . fromInteger
>           | otherwise =
>               Apply (prelFromInteger ty) . Literal integerType . Integer
> desugarLiteral ty (Rational r) = Right (fixLiteral ty r)
>   where fixLiteral (TypeConstrained tys _) = fixLiteral (head tys)
>         fixLiteral ty'
>           | ty' == floatType = Literal ty . Rational
>           | ty' == rationalType = desugarRatio
>           | otherwise = Apply (prelFromRational ty) . desugarRatio
> desugarLiteral ty (String cs) =
>   Left (List ty (map (Literal (elemType ty) . Char) cs))

> desugarRatio :: Rational -> Expression Type
> desugarRatio r =
>   foldl applyToInteger (ratioConstr integerType) [numerator r,denominator r]
>   where applyToInteger e = Apply e . Literal integerType . Integer

> desugarExpr :: ModuleIdent -> Position -> Expression Type
>             -> DesugarState (Expression Type)
> desugarExpr m p (Literal ty l) =
>   either (desugarExpr m p) return (desugarLiteral ty l)
> desugarExpr m p (Variable ty v)
>   -- NB The name of the initial goal is anonId (not renamed, cf. goalModule
>   --    in module Goals) and must not be changed
>   | isRenamed v' && unRenameIdent v' == anonId =
>       do
>         v'' <- freshVar m "_#var" ty
>         return (Let [FreeDecl p [snd v'']] (uncurry mkVar v''))
>   | otherwise = return (Variable ty v)
>   where v' = unqualify v
> desugarExpr _ _ (Constructor ty c) = return (Constructor ty c)
> desugarExpr m p (Paren e) = desugarExpr m p e
> desugarExpr m p (Typed e _) = desugarExpr m p e
> desugarExpr m p (Record ty c fs) =
>   liftM (Record ty c) (mapM (desugarField (desugarExpr m p)) fs)
> desugarExpr m p (RecordUpdate e fs) =
>   liftM2 RecordUpdate
>          (desugarExpr m p e)
>          (mapM (desugarField (desugarExpr m p)) fs)
> desugarExpr m p (Tuple es) =
>   liftM (apply (Constructor ty (qTupleId (length es))))
>         (mapM (desugarExpr m p) es)
>   where ty = foldr TypeArrow (tupleType tys) tys
>         tys = map typeOf es
> desugarExpr m p (List ty es) =
>   liftM (foldr cons nil) (mapM (desugarExpr m p) es)
>   where nil = Constructor ty qNilId
>         cons = Apply . Apply (Constructor (consType (elemType ty)) qConsId)
> desugarExpr m p (ListCompr e []) =
>   desugarExpr m p (List (listType (typeOf e)) [e])
> desugarExpr m p (ListCompr e (q:qs)) = desugarQual m p q (ListCompr e qs)
> desugarExpr m p (EnumFrom e) =
>   liftM (Apply (prelEnumFrom (typeOf e))) (desugarExpr m p e)
> desugarExpr m p (EnumFromThen e1 e2) =
>   liftM (apply (prelEnumFromThen (typeOf e1)))
>         (mapM (desugarExpr m p) [e1,e2])
> desugarExpr m p (EnumFromTo e1 e2) =
>   liftM (apply (prelEnumFromTo (typeOf e1))) (mapM (desugarExpr m p) [e1,e2])
> desugarExpr m p (EnumFromThenTo e1 e2 e3) =
>   liftM (apply (prelEnumFromThenTo (typeOf e1)))
>         (mapM (desugarExpr m p) [e1,e2,e3])
> desugarExpr m p (UnaryMinus e) =
>   liftM (Apply (prelNegate (typeOf e))) (desugarExpr m p e)
> desugarExpr m p (Apply e1 e2) =
>   liftM2 Apply (desugarExpr m p e1) (desugarExpr m p e2)
> desugarExpr m p (InfixApply e1 op e2) =
>   do
>     op' <- desugarExpr m p (infixOp op)
>     e1' <- desugarExpr m p e1
>     e2' <- desugarExpr m p e2
>     return (Apply (Apply op' e1') e2')
> desugarExpr m p (LeftSection e op) =
>   do
>     op' <- desugarExpr m p (infixOp op)
>     e' <- desugarExpr m p e
>     return (Apply op' e')
> desugarExpr m p (RightSection op e) =
>   do
>     op' <- desugarExpr m p (infixOp op)
>     e' <- desugarExpr m p e
>     return (Apply (Apply (prelFlip ty1 ty2 ty3) op') e')
>   where TypeArrow ty1 (TypeArrow ty2 ty3) = typeOf (infixOp op)
> desugarExpr m _ (Lambda p ts e) =
>   liftM2 (Lambda p) (mapM (desugarTerm m) ts) (desugarExpr m p e)
> desugarExpr m p (Let ds e) =
>   liftM2 Let (desugarDeclGroup m ds) (desugarExpr m p e)
> desugarExpr m p (Do sts e) = desugarExpr m p (foldr desugarStmt e sts)
>   where desugarStmt (StmtExpr e) e' =
>           apply (prelBind_ (typeOf e) (typeOf e')) [e,e']
>         desugarStmt (StmtBind p t e) e' =
>           apply (prelBind (typeOf e) (typeOf t) (typeOf e'))
>                 [e,Lambda p [t] e']
>         desugarStmt (StmtDecl ds) e' = mkLet ds e'
> desugarExpr m p (IfThenElse e1 e2 e3) =
>   liftM3 IfThenElse
>          (desugarExpr m p e1)
>          (desugarExpr m p e2)
>          (desugarExpr m p e3)
> desugarExpr m p (Case e as) =
>   liftM2 Case (desugarExpr m p e) (mapM (desugarAlt m) as)
> desugarExpr m p (Fcase e as) =
>   liftM2 Fcase (desugarExpr m p e) (mapM (desugarAlt m) as)

> desugarAlt :: ModuleIdent -> Alt Type -> DesugarState (Alt Type)
> desugarAlt m (Alt p t rhs) =
>   liftM2 (Alt p) (desugarTerm m t) (desugarRhs m rhs)

> desugarField :: (a -> DesugarState a) -> Field a -> DesugarState (Field a)
> desugarField desugar (Field l e) = liftM (Field l) (desugar e)

\end{verbatim}
In general, a list comprehension of the form
\texttt{[}$e$~\texttt{|}~$t$~\texttt{<-}~$l$\texttt{,}~\emph{qs}\texttt{]}
is transformed into an expression \texttt{foldr}~$f$~\texttt{[]}~$l$ where $f$
is a new function defined as
\begin{quote}
  \begin{tabbing}
    $f$ $x$ \emph{xs} \texttt{=} \\
    \quad \= \texttt{case} $x$ \texttt{of} \\
          \> \quad \= $t$ \texttt{->} \texttt{[}$e$ \texttt{|} \emph{qs}\texttt{]} \texttt{++} \emph{xs} \\
          \>       \> \texttt{\_} \texttt{->} \emph{xs}
  \end{tabbing}
\end{quote}
Note that this translation evaluates the elements of $l$ rigidly,
whereas the translation given in the Curry report is flexible.
However, it does not seem very useful to have the comprehension
generate instances of $t$ which do not contribute to the list.

Actually, we generate slightly better code in a few special cases.
When $t$ is a plain variable, the \texttt{case} expression degenerates
into a let-binding and the auxiliary function thus becomes an alias
for \texttt{(++)}. Instead of \texttt{foldr~(++)} we use the
equivalent Prelude function \texttt{concatMap}. In addition, if the
remaining list comprehension in the body of the auxiliary function has
no qualifiers -- i.e., if it is equivalent to \texttt{[$e$]} -- we
avoid the construction of the singleton list by calling \texttt{(:)}
instead of \texttt{(++)} and \texttt{map} in place of
\texttt{concatMap}, respectively.
\begin{verbatim}

> desugarQual :: ModuleIdent -> Position -> Statement Type -> Expression Type
>             -> DesugarState (Expression Type)
> desugarQual m p (StmtExpr b) e =
>   desugarExpr m p (IfThenElse b e (List (typeOf e) []))
> desugarQual m _ (StmtBind p t l) e
>   | isVarPattern t = desugarExpr m p (qualExpr t e l)
>   | otherwise =
>       do
>         (ty,v) <- freshVar m "_#var" (typeOf t)
>         (ty',l') <- freshVar m "_#var" (typeOf e)
>         desugarExpr m p
>           (apply (prelFoldr ty ty') [foldFunct ty v ty' l' e,List ty' [],l])
>   where qualExpr v (ListCompr e []) l =
>           apply (prelMap (typeOf v) (typeOf e)) [Lambda p [v] e,l]
>         qualExpr v e l =
>           apply (prelConcatMap (typeOf v) (elemType (typeOf e)))
>                 [Lambda p [v] e,l]
>         foldFunct ty v ty' l e =
>           Lambda p [VariablePattern ty v,VariablePattern ty' l]
>             (Case (mkVar ty v)
>                   [caseAlt p t (append (elemType ty') e (mkVar ty' l)),
>                    caseAlt p (VariablePattern ty v) (mkVar ty' l)])
>         append ty (ListCompr e []) l =
>           apply (Constructor (consType ty) qConsId) [e,l]
>         append ty e l = apply (prelAppend ty) [e,l]
> desugarQual m p (StmtDecl ds) e = desugarExpr m p (mkLet ds e)

\end{verbatim}
Generation of fresh names.
\begin{verbatim}

> freshVar :: ModuleIdent -> String -> Type -> DesugarState (Type,Ident)
> freshVar m prefix ty =
>   do
>     v <- liftM (mkName prefix) (liftSt (updateSt (1 +)))
>     updateSt_ (bindFun m v 0 (monoType ty))
>     return (ty,v)
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
> prelMap a b = preludeFun [a `TypeArrow` b,listType a] (listType b) "map"
> prelFoldr a b =
>   preludeFun [a `TypeArrow` (b `TypeArrow` b),b,listType a] b "foldr"
> prelAppend a = preludeFun [listType a,listType a] (listType a) "++"
> prelConcatMap a b =
>   preludeFun [a `TypeArrow` listType b,listType a] (listType b) "concatMap"
> prelNegate a = preludeFun [a] a "negate"

> preludeFun :: [Type] -> Type -> String -> Expression Type
> preludeFun tys ty f =
>   Variable (foldr TypeArrow ty tys) (qualifyWith preludeMIdent (mkIdent f))

> ratioConstr :: Type -> Expression Type
> ratioConstr a =
>   Constructor (TypeArrow a (TypeArrow a (ratioType a)))
>               (qualifyWith ratioMIdent (mkIdent ":%"))

\end{verbatim}
Auxiliary definitions.
\begin{verbatim}

> consType :: Type -> Type
> consType a = TypeArrow a (TypeArrow (listType a) (listType a))

> elemType :: Type -> Type
> elemType (TypeApply (TypeConstructor tc) ty) | tc == qListId = ty
> elemType ty = internalError ("elemType " ++ show ty)

\end{verbatim}
