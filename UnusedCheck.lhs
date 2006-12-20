% -*- LaTeX -*-
% $Id: UnusedCheck.lhs 2052 2006-12-20 11:37:05Z wlux $
%
% Copyright (c) 2005-2006, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{UnusedCheck.lhs}
\section{Checking for Unused Variables}
After syntax checking and renaming, the compiler can optionally report
unused data constructors, functions, and variables in the source code.
Note that we do not check for unused type constructors and type
variables at present.
\begin{verbatim}

> module UnusedCheck(unusedCheck,unusedCheckGoal) where
> import Base hiding(TypeKind(..), ValueKind(..))
> import Set
> import Options

\end{verbatim}
In order to report unused variables in a module, we first compute the
set of all used variables in the module. Using the resulting set we
then check for unused variables in the code and report warnings for
them according to the compiler options.
\begin{verbatim}

> unusedCheck :: [Warn] -> Module a -> [String]
> unusedCheck us (Module m (Just (Exporting _ es)) _ ds) =
>   reportUnused us $ unused (used m es (used m ds zeroSet)) noPosition ds []
>   where noPosition = error "noPosition"

> unusedCheckGoal :: [Warn] -> Goal a -> [String]
> unusedCheckGoal us (Goal p e ds) =
>   reportUnused us $ unused (used emptyMIdent g' zeroSet) p g' []
>   where g' = SimpleRhs p e ds

> reportUnused :: [Warn] -> [Undef] -> [String]
> reportUnused us = map format . unusedFilter us

> data Undef =
>     Data Position Ident
>   | Decl Position Ident
>   | Meth Position Ident
>   | Var Position Ident
>   | Pattern Position
>   deriving (Eq,Show)

> unusedFilter :: [Warn] -> [Undef] -> [Undef]
> unusedFilter us vs
>   | null (filter (`elem` [minUnused..maxUnused]) us) = []
>   | otherwise = filter warn vs
>   where warn (Data _ _) = WarnUnusedData `elem` us
>         warn (Decl _ _) = WarnUnusedDecl `elem` us
>         warn (Meth _ _) = WarnUnusedDecl `elem` us
>         warn (Var _ _) = WarnUnusedVar `elem` us
>         warn (Pattern _) = WarnUnusedDecl `elem` us

> format :: Undef -> String
> format (Data p c) = atP p ("Warning: unused data constructor " ++ name c)
> format (Decl p x) = atP p ("Warning: unused variable " ++ name x)
> format (Meth p f) = atP p ("Warning: unused method " ++ name f)
> format (Var p x) = atP p ("Warning: unused variable " ++ name x)
> format (Pattern p) = atP p "Warning: unused pattern declaration"

> unusedVars :: (Position -> Ident -> Undef) -> Set Ident -> Position -> [Ident]
>            -> [Undef] -> [Undef]
> unusedVars unused used p xs = ([unused p x | x <- xs, x `notElemSet` used] ++)

\end{verbatim}
Collecting used identifiers and filtering unused ones are each
implemented by a traversal of the syntax tree.
\begin{verbatim}

> class SyntaxTree a where
>   used :: ModuleIdent -> a -> Set Ident -> Set Ident
>   unused :: Set Ident -> Position -> a -> [Undef] -> [Undef]

> instance SyntaxTree a => SyntaxTree [a] where
>   used _ [] = id
>   used m (x:xs) = used m x . used m xs
>   unused used p xs ys = foldr (unused used p) ys xs

> instance SyntaxTree Export where
>   used m (Export x) = used m x
>   used m (ExportTypeWith tc xs) = used m (map (qualifyLike tc) xs)
>   unused _ _ _ = id

> instance SyntaxTree (TopDecl a) where
>   used _ (DataDecl _ _ _ _ _ _) = id
>   used _ (NewtypeDecl _ _ _ _ _ _) = id
>   used _ (TypeDecl _ _ _ _) = id
>   used m (ClassDecl _ _ _ _ ds) = used m ds
>   used m (InstanceDecl _ _ _ _ ds) = used m ds
>   used m (BlockDecl d) = used m d

>   unused used p (DataDecl _ _ _ _ cs _) = unused used p cs
>   unused used p (NewtypeDecl _ _ _ _ nc _) = unused used p nc
>   unused _ _ (TypeDecl _ _ _ _) = id
>   unused used _ (ClassDecl p _ _ _ ds) = unused used p ds
>   unused used _ (InstanceDecl p _ _ _ ds) = unused used p ds
>   unused used p (BlockDecl d) = unused used p d

> instance SyntaxTree ConstrDecl where
>   used _ _ = id
>   unused used _ (ConstrDecl p _ c _) = unusedVars Data used p [c]
>   unused used _ (ConOpDecl p _ _ op _) = unusedVars Data used p [op]

> instance SyntaxTree NewConstrDecl where
>   used _ _ = id
>   unused used _ (NewConstrDecl p c _) = unusedVars Data used p [c]

> instance SyntaxTree (MethodDecl a) where
>   used _ (MethodFixity _ _ _ _) = id
>   used _ (MethodSig _ _ _) = id
>   used m (MethodDecl _ _ eqs) = used m eqs
>   used _ (TrustMethod _ _ _) = id
>   unused _ _ (MethodFixity _ _ _ _) = id
>   unused used _ (MethodSig p fs _) = unusedVars Meth used p fs
>   unused used _ (MethodDecl p _ eqs) = unused used p eqs
>   unused _ _ (TrustMethod _ _ _) = id

> instance SyntaxTree (Decl a) where
>   used m (FunctionDecl _ _ eqs) = used m eqs
>   used m (PatternDecl _ t rhs) = used m t . used m rhs
>   used _ _ = id
>
>   unused used _ (FunctionDecl p f eqs) =
>     unusedVars Decl used p [f] . unused used p eqs
>   unused used _ (ForeignDecl p _ _ f _) = unusedVars Decl used p [f]
>   unused used _ (PatternDecl p (VariablePattern _ v) rhs)
>     | isAnonId v = ([Pattern p] ++)
>     | otherwise = unusedVars Decl used p [v]
>   unused used _ (PatternDecl p t rhs) =
>      ([Pattern p | not (any (`elemSet` used) bvs)] ++) .
>      unusedVars Var used p bvs . unused used p rhs
>     where bvs = filter (not . isAnonId) (bv t)
>   unused used _ (FreeDecl p xs) = unusedVars Decl used p xs
>   unused _ _ _ = id

> instance SyntaxTree (Equation a) where
>   used m (Equation _ lhs rhs) = used m lhs . used m rhs
>   unused used _ (Equation p lhs rhs) = unused used p lhs . unused used p rhs

> instance SyntaxTree (Lhs a) where
>   used m (FunLhs _ ts) = used m ts
>   used m (OpLhs t1 _ t2) = used m t1 . used m t2
>   used m (ApLhs lhs ts) = used m lhs . used m ts
>   unused used p lhs = unusedVars Var used p (filter (not . isAnonId) (bv lhs))

> instance SyntaxTree (ConstrTerm a) where
>   used _ (LiteralPattern _ _) = id
>   used _ (NegativePattern _ _) = id
>   used _ (VariablePattern _ _) = id
>   used m (ConstructorPattern _ c ts) = used m c . used m ts
>   used m (InfixPattern _ t1 op t2) = used m t1 . used m op . used m t2
>   used m (ParenPattern t) = used m t
>   used m (TuplePattern ts) = used m ts
>   used m (ListPattern _ ts) = used m ts
>   used m (AsPattern _ t) = used m t
>   used m (LazyPattern t) = used m t
>
>   unused used p t = unusedVars Var used p (filter (not . isAnonId) (bv t))

> instance SyntaxTree (Rhs a) where
>   used m (SimpleRhs _ e ds) = used m ds . used m e
>   used m (GuardedRhs es ds) = used m ds . used m es
>   unused used _ (SimpleRhs p e ds) = unused used p ds . unused used p e
>   unused used p (GuardedRhs es ds) = unused used p ds . unused used p es

> instance SyntaxTree (CondExpr a) where
>   used m (CondExpr _ g e) = used m g . used m e
>   unused used _ (CondExpr p g e) = unused used p g . unused used p e

> instance SyntaxTree (Expression a) where
>   used _ (Literal _ _) = id
>   used m (Variable _ x) = used m x
>   used m (Constructor _ c) = used m c
>   used m (Paren e) = used m e
>   used m (Typed e _) = used m e
>   used m (Tuple es) = used m es
>   used m (List _ es) = used m es
>   used m (ListCompr e qs) = used m qs . used m e
>   used m (EnumFrom e) = used m e
>   used m (EnumFromThen e1 e2) = used m e1 . used m e2
>   used m (EnumFromTo e1 e2) = used m e1 . used m e2
>   used m (EnumFromThenTo e1 e2 e3) = used m e1 . used m e2 . used m e3
>   used m (UnaryMinus e) = used m e
>   used m (Apply e1 e2) = used m e1 . used m e2
>   used m (InfixApply e1 op e2) = used m e1 . used m (opName op) . used m e2
>   used m (LeftSection e op) = used m e . used m (opName op)
>   used m (RightSection op e) = used m (opName op) . used m e
>   used m (Lambda ts e) = used m ts . used m e
>   used m (Let ds e) = used m ds . used m e
>   used m (Do sts e) = used m sts . used m e
>   used m (IfThenElse e1 e2 e3) = used m e1 . used m e2 . used m e3
>   used m (Case e as) = used m e . used m as
>
>   unused _ _ (Literal _ _) = id
>   unused _ _ (Variable _ _) = id
>   unused _ _ (Constructor _ _) = id
>   unused used p (Paren e) = unused used p e
>   unused used p (Typed e _) = unused used p e
>   unused used p (Tuple es) = unused used p es
>   unused used p (List _ es) = unused used p es
>   unused used p (ListCompr e qs) = unused used p qs . unused used p e
>   unused used p (EnumFrom e) = unused used p e
>   unused used p (EnumFromThen e1 e2) = unused used p e1 . unused used p e2
>   unused used p (EnumFromTo e1 e2) = unused used p e1 . unused used p e2
>   unused used p (EnumFromThenTo e1 e2 e3) =
>     unused used p e1 . unused used p e2 . unused used p e3
>   unused used p (UnaryMinus e) = unused used p e
>   unused used p (Apply e1 e2) = unused used p e1 . unused used p e2
>   unused used p (InfixApply e1 _ e2) = unused used p e1 . unused used p e2
>   unused used p (LeftSection e _) = unused used p e
>   unused used p (RightSection _ e) = unused used p e
>   unused used p (Lambda ts e) = unused used p ts . unused used p e
>   unused used p (Let ds e) = unused used p ds . unused used p e
>   unused used p (Do sts e) = unused used p sts . unused used p e
>   unused used p (IfThenElse e1 e2 e3) =
>     unused used p e1 . unused used p e2 . unused used p e3
>   unused used p (Case e as) = unused used p e . unused used p as

> instance SyntaxTree (Statement a) where
>   used m (StmtExpr e) = used m e
>   used m (StmtBind t e) = used m t . used m e
>   used m (StmtDecl ds) = used m ds
>   unused used p (StmtExpr e) = unused used p e
>   unused used p (StmtBind t e) = unused used p t . unused used p e
>   unused used p (StmtDecl ds) = unused used p ds

> instance SyntaxTree (Alt a) where
>   used m (Alt _ t rhs) = used m t . used m rhs
>   unused used _ (Alt p t rhs) = unused used p t . unused used p rhs

> instance SyntaxTree QualIdent where
>   used m x =
>     case splitQualIdent (qualUnqualify m x) of
>       (Just _,_) -> id
>       (Nothing,x') -> addToSet x'
>   unused _ _ _ = id

\end{verbatim}
Anonymous identifiers in patterns are always ignored.
\begin{verbatim}

> isAnonId :: Ident -> Bool
> isAnonId x = unRenameIdent x == anonId

\end{verbatim}
