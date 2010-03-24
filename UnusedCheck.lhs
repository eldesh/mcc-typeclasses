% -*- LaTeX -*-
% $Id: UnusedCheck.lhs 2931 2010-03-24 09:14:11Z wlux $
%
% Copyright (c) 2005-2010, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{UnusedCheck.lhs}
\section{Checking for Unused Variables}
After syntax checking and before renaming, the compiler can optionally
report unused data constructors, functions, and variables in the
source code. Note that we do not check for unused type constructors
and type variables at present.
\begin{verbatim}

> module UnusedCheck(unusedCheck,unusedCheckGoal) where
> import Base
> import Curry
> import CurryUtils
> import Options
> import Position
> import Set
> import Utils

\end{verbatim}
Since local variables have not yet been renamed, we compute the set of
used variables together with the list of unused variables. In
particular, whenever a scope is left we collect the unused variables
of that scope and remove their identifiers from the set of used
variables. At the end, we report warnings for the unused variables
according to the compiler options.
\begin{verbatim}

> unusedCheck :: [Warn] -> Module a -> [String]
> unusedCheck us (Module m (Just (Exporting _ es)) _ ds) =
>   reportUnused us $
>   snd (checkUnused noPosition ds . used m es . used m ds $ (zeroSet,[]))

> unusedCheckGoal :: [Warn] -> ModuleIdent -> Goal a -> [String]
> unusedCheckGoal us m (Goal p e ds) =
>   reportUnused us $ snd (used m g' $ (zeroSet,[]))
>   where g' = SimpleRhs p e ds

> reportUnused :: [Warn] -> [Undef] -> [String]
> reportUnused us = map format . unusedFilter us

> data Undef =
>     Data Position Ident
>   | Label Position Ident
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
>         warn (Label _ _) = WarnUnusedData `elem` us
>         warn (Decl _ _) = WarnUnusedDecl `elem` us
>         warn (Meth _ _) = WarnUnusedDecl `elem` us
>         warn (Var _ _) = WarnUnusedVar `elem` us
>         warn (Pattern _) = WarnUnusedDecl `elem` us

> format :: Undef -> String
> format (Data p c) = atP p ("Warning: unused data constructor " ++ name c)
> format (Label p l) = atP p ("Warning: unused field label " ++ name l)
> format (Decl p x) = atP p ("Warning: unused variable " ++ name x)
> format (Meth p f) = atP p ("Warning: unused method " ++ name f)
> format (Var p x) = atP p ("Warning: unused variable " ++ name x)
> format (Pattern p) = atP p "Warning: unused pattern declaration"

> unusedVars :: (Position -> Ident -> Undef) -> Set Ident -> Position -> [Ident]
>            -> [Undef] -> [Undef]
> unusedVars unused used p xs = ([unused p x | x <- xs, x `notElemSet` used] ++)

\end{verbatim}
Collecting used identifiers and filtering unused ones are implemented
by a traversal of the syntax tree.
\begin{verbatim}

> type U = (Set Ident,[Undef])

> class SyntaxTree a where
>   used :: ModuleIdent -> a -> U -> U

> instance SyntaxTree a => SyntaxTree [a] where
>   used _ [] = id
>   used m (x:xs) = used m x . used m xs

> instance SyntaxTree Export where
>   used m (Export x) = used m x
>   used m (ExportTypeWith tc xs) = used m (map (qualifyLike tc) xs)

> instance SyntaxTree (TopDecl a) where
>   used _ (DataDecl _ _ _ _ _ _) = id
>   used _ (NewtypeDecl _ _ _ _ _ _) = id
>   used _ (TypeDecl _ _ _ _) = id
>   used m (ClassDecl _ _ _ _ ds) = used m ds
>   used m (InstanceDecl _ _ _ _ ds) = used m ds
>   used m (DefaultDecl _ _) = id
>   used m (BlockDecl d) = used m d
>   used _ (SplitAnnot _) = id

> instance SyntaxTree (Decl a) where
>   used _ (InfixDecl _ _ _ _) = id
>   used _ (TypeSig _ _ _) = id
>   used m (FunctionDecl _ f eqs) = nest (apFst (deleteFromSet f) . used m eqs)
>   used _ (ForeignDecl _ _ _ _ _ _) = id
>   used m (PatternDecl _ t rhs) =
>     case t of
>       VariablePattern _ v -> nest (apFst (deleteFromSet v) . used m rhs)
>       _ -> used m t . used m rhs
>   used _ (FreeDecl _ _) = id
>   used _ (TrustAnnot _ _ _) = id

> instance SyntaxTree (Equation a) where
>   used m (Equation p lhs rhs) =
>     nest (checkUnused p lhs . used m lhs . used m rhs)

> instance SyntaxTree (Lhs a) where
>   used m (FunLhs _ ts) = used m ts
>   used m (OpLhs t1 _ t2) = used m t1 . used m t2
>   used m (ApLhs lhs ts) = used m lhs . used m ts

> instance SyntaxTree (ConstrTerm a) where
>   used _ (LiteralPattern _ _) = id
>   used _ (NegativePattern _ _) = id
>   used _ (VariablePattern _ _) = id
>   used m (ConstructorPattern _ c ts) = used m c . used m ts
>   used m (FunctionPattern _ f ts) = used m f . used m ts
>   used m (InfixPattern _ t1 op t2) =
>     used m t1 . used m (opName op) . used m t2
>   used m (ParenPattern t) = used m t
>   used m (RecordPattern _ c fs) = used m c . used m fs
>   used m (TuplePattern ts) = used m ts
>   used m (ListPattern _ ts) = used m ts
>   used m (AsPattern _ t) = used m t
>   used m (LazyPattern t) = used m t

> instance SyntaxTree (Rhs a) where
>   used m (SimpleRhs p e ds) = nest (checkUnused p ds . used m ds . used m e)
>   used m (GuardedRhs es ds) =
>     nest (checkUnused noPosition ds . used m ds . used m es)

> instance SyntaxTree (CondExpr a) where
>   used m (CondExpr _ g e) = used m g . used m e

> instance SyntaxTree (Expression a) where
>   used _ (Literal _ _) = id
>   used m (Variable _ x) = used m x
>   used m (Constructor _ c) = used m c
>   used m (Paren e) = used m e
>   used m (Typed e _) = used m e
>   used m (Record _ c fs) = used m c . used m fs
>   used m (RecordUpdate e fs) = used m e . used m fs
>   used m (Tuple es) = used m es
>   used m (List _ es) = used m es
>   used m (ListCompr e qs) = nest (used m qs . used m e)
>   used m (EnumFrom e) = used m e
>   used m (EnumFromThen e1 e2) = used m e1 . used m e2
>   used m (EnumFromTo e1 e2) = used m e1 . used m e2
>   used m (EnumFromThenTo e1 e2 e3) = used m e1 . used m e2 . used m e3
>   used m (UnaryMinus e) = used m e
>   used m (Apply e1 e2) = used m e1 . used m e2
>   used m (InfixApply e1 op e2) = used m e1 . used m (opName op) . used m e2
>   used m (LeftSection e op) = used m e . used m (opName op)
>   used m (RightSection op e) = used m (opName op) . used m e
>   used m (Lambda p ts e) = nest (checkUnused p ts . used m ts . used m e)
>   used m (Let ds e) = nest (checkUnused noPosition ds . used m ds . used m e)
>   used m (Do sts e) = nest (used m sts . used m e)
>   used m (IfThenElse e1 e2 e3) = used m e1 . used m e2 . used m e3
>   used m (Case e as) = used m e . used m as
>   used m (Fcase e as) = used m e . used m as

> instance SyntaxTree (Statement a) where
>   used m (StmtExpr e) = used m e
>   used m (StmtBind p t e) = used m e . checkUnused p t . used m t
>   used m (StmtDecl ds) = checkUnused noPosition ds . used m ds

> instance SyntaxTree (Alt a) where
>   used m (Alt p t rhs) = nest (checkUnused p t . used m t . used m rhs)

> instance SyntaxTree a => SyntaxTree (Field a) where
>   used m (Field l x) = used m l . used m x

> instance SyntaxTree QualIdent where
>   used m x =
>     case splitQualIdent (qualUnqualify m x) of
>       (Just _,_) -> id
>       (Nothing,x') -> apFst (addToSet x')

\end{verbatim}
Within each scope, we check for unused variables and then remove the
set of bound variables from the list of used variables. The functions
\texttt{nest}, which isolates an expression from its right neighbor,
and \texttt{checkUnused}, which actually checks for unused variables,
are kept separate in order to handle qualifiers in list comprehensions
and statement sequences in do expressions correctly. Recall that for a
statement sequence $t \leftarrow e; \emph{sts}$, the variables used in
\emph{sts} (but not those in $e$) are relevant for determining the
unused variables of pattern $t$.
\begin{verbatim}

> nest :: (U -> U) -> U -> U
> nest used (vs,us) = (vs' `unionSet` vs,us')
>   where (vs',us') = used (zeroSet,us)

> checkUnused :: (QuantExpr a,Binder a) => Position -> a -> U -> U
> checkUnused p x (vs,us) = (foldr deleteFromSet vs (bv x),unused vs p x us)

> class Binder a where
>   unused :: Set Ident -> Position -> a -> [Undef] -> [Undef]

> instance Binder a => Binder [a] where
>   unused used p xs ys = foldr (unused used p) ys xs

> instance Binder (TopDecl a) where
>   unused used p (DataDecl _ _ _ _ cs _) = unused used p cs
>   unused used p (NewtypeDecl _ _ _ _ nc _) = unused used p nc
>   unused _ _ (TypeDecl _ _ _ _) = id
>   unused used _ (ClassDecl p _ _ _ ds) =
>     flip (foldr ($)) [unusedVars Meth used p fs | TypeSig p fs _ <- ds]
>   unused _ _ (InstanceDecl _ _ _ _ _) = id
>   unused _ _ (DefaultDecl _ _) = id
>   unused used p (BlockDecl d) = unused used p d
>   unused _ _ (SplitAnnot _) = id

> instance Binder ConstrDecl where
>   unused used _ (ConstrDecl p _ _ c _) = unusedVars Data used p [c]
>   unused used _ (ConOpDecl p _ _ _ op _) = unusedVars Data used p [op]
>   unused used _ (RecordDecl p _ _ c fs) =
>     unusedVars Data used p [c] . unused used p fs

> instance Binder FieldDecl where
>   unused used _ (FieldDecl p ls _) = unusedVars Label used p ls

> instance Binder NewConstrDecl where
>   unused used _ (NewConstrDecl p c _) = unusedVars Data used p [c]
>   unused used _ (NewRecordDecl p c l _) =
>     unusedVars Data used p [c] . unusedVars Label used p [l]

> instance Binder (Decl a) where
>   unused _ _ (InfixDecl _ _ _ _) = id
>   unused _ _ (TypeSig _ _ _) = id
>   unused used _ (FunctionDecl p f _) = unusedVars Decl used p [f]
>   unused used _ (ForeignDecl p _ _ _ f _) = unusedVars Decl used p [f]
>   unused used _ (PatternDecl p t rhs) =
>     case t of
>       VariablePattern _ v
>         | v == anonId -> ([Pattern p] ++)
>         | otherwise -> unusedVars Decl used p [v]
>       _ ->
>         ([Pattern p | not (any (`elemSet` used) bvs)] ++) .
>         unusedVars Var used p bvs
>     where bvs = bv t
>   unused used _ (FreeDecl p xs) = unusedVars Decl used p xs
>   unused _ _ (TrustAnnot _ _ _) = id

> instance Binder (Lhs a) where
>   unused used p lhs = unusedVars Var used p (bv lhs)

> instance Binder (ConstrTerm a) where
>   unused used p t = unusedVars Var used p (bv t)

\end{verbatim}
Auxiliary functions.
\begin{verbatim}

> noPosition :: Position
> noPosition = error "noPosition"

\end{verbatim}
