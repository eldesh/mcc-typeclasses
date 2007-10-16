% -*- LaTeX -*-
% $Id: OverlapCheck.lhs 2507 2007-10-16 22:24:05Z wlux $
%
% Copyright (c) 2006-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{OverlapCheck.lhs}
\section{Checking for Rules with Overlapping Patterns}
The compiler can also report rules with overlapping left hand side
patterns, which causes a non-deterministic evaluation of the
corresponding functions.
\begin{verbatim}

> module OverlapCheck(overlapCheck, overlapCheckGoal) where
> import Base
> import Curry
> import CurryUtils
> import List
> import Options
> import Position
> import Utils

> overlapCheck :: [Warn] -> Module a -> [String]
> overlapCheck v (Module m _ _ ds) = report v $ overlap noPosition ds []
>   where noPosition = error "noPosition"

> overlapCheckGoal :: [Warn] -> Goal a -> [String]
> overlapCheckGoal v (Goal p e ds) = report v $ overlap p (SimpleRhs p e ds) []

> report :: [Warn] -> [P Ident] -> [String]
> report ws
>   | WarnOverlap `elem` ws = map format
>   | otherwise = const []

> format :: P Ident -> String
> format (P p x) =
>   atP p ("Warning: " ++ name x ++ " has overlapping rules")

\end{verbatim}
The names of the functions with overlapping left hand side patterns
are collected with a simple traversal of the syntax tree.
\begin{verbatim}

> class Syntax a where
>   overlap :: Position -> a -> [P Ident] -> [P Ident]

> instance Syntax a => Syntax [a] where
>   overlap p xs ys = foldr (overlap p) ys xs

> instance Syntax (TopDecl a) where
>   overlap _ (DataDecl _ _ _ _ _ _) = id
>   overlap _ (NewtypeDecl _ _ _ _ _ _) = id
>   overlap _ (TypeDecl _ _ _ _) = id
>   overlap _ (ClassDecl p _ _ _ ds) = overlap p ds 
>   overlap _ (InstanceDecl p _ _ _ ds) = overlap p ds 
>   overlap _ (DefaultDecl _ _) = id
>   overlap p (BlockDecl d) = overlap p d

> instance Syntax (Decl a) where
>   overlap _ (InfixDecl _ _ _ _) = id
>   overlap _ (TypeSig _ _ _) = id
>   overlap _ (FunctionDecl p f eqs) =
>     ([P p f | isNonDet eqs] ++) . overlap p eqs
>   overlap _ (ForeignDecl _ _ _ _ _ _) = id
>   overlap _ (PatternDecl p _ rhs) = overlap p rhs
>   overlap _ (FreeDecl _ _) = id
>   overlap _ (TrustAnnot _ _ _) = id

> instance Syntax (Equation a) where
>   overlap _ (Equation p _ rhs) = overlap p rhs

> instance Syntax (Rhs a) where
>   overlap _ (SimpleRhs p e ds) = overlap p ds . overlap p e
>   overlap p (GuardedRhs es ds) = overlap p ds . overlap p es

> instance Syntax (CondExpr a) where
>   overlap _ (CondExpr p g e) = overlap p g . overlap p e

> instance Syntax (Expression a) where
>   overlap _ (Literal _ _) = id
>   overlap _ (Variable _ _) = id
>   overlap _ (Constructor _ _) = id
>   overlap p (Paren e) = overlap p e
>   overlap p (Typed e _) = overlap p e
>   overlap p (Tuple es) = overlap p es
>   overlap p (List _ es) = overlap p es
>   overlap p (ListCompr e qs) = overlap p qs . overlap p e
>   overlap p (EnumFrom e) = overlap p e
>   overlap p (EnumFromThen e1 e2) = overlap p e1 . overlap p e2
>   overlap p (EnumFromTo e1 e2) = overlap p e1 . overlap p e2
>   overlap p (EnumFromThenTo e1 e2 e3) =
>     overlap p e1 . overlap p e2 . overlap p e3
>   overlap p (UnaryMinus e) = overlap p e
>   overlap p (Apply e1 e2) = overlap p e1 . overlap p e2
>   overlap p (InfixApply e1 _ e2) = overlap p e1 . overlap p e2
>   overlap p (LeftSection e _) = overlap p e
>   overlap p (RightSection _ e) = overlap p e
>   overlap _ (Lambda p _ e) = overlap p e
>   overlap p (Let ds e) = overlap p ds . overlap p e
>   overlap p (Do sts e) = overlap p sts . overlap p e
>   overlap p (IfThenElse e1 e2 e3) =
>     overlap p e1 . overlap p e2 . overlap p e3
>   overlap p (Case e as) = overlap p e . overlap p as

> instance Syntax (Statement a) where
>   overlap p (StmtExpr e) = overlap p e
>   overlap _ (StmtBind p _ e) = overlap p e
>   overlap p (StmtDecl ds) = overlap p ds

> instance Syntax (Alt a) where
>   overlap _ (Alt p _ rhs) = overlap p rhs

\end{verbatim}
The code checking whether a function has rules with overlapping
patterns is essentially a simplified version of the pattern matching
algorithm implemented in module \texttt{ILTrans} (see
Sect.~\ref{sec:il-trans}). The code assumes that the program is type
correct and accordingly promotes integer constants to floating-point
when necessary.
\begin{verbatim}

> isNonDet :: [Equation a] -> Bool
> isNonDet eqs =
>   isOverlap [map desugar (snd (flatLhs lhs)) | Equation _ lhs _ <- eqs]

> isOverlap :: [[ConstrTerm ()]] -> Bool
> isOverlap (ts:tss) =
>   not (null tss) &&
>   case matchInductive (ts:tss) of
>      [] -> True
>      tss:_ -> any isOverlap tss

> matchInductive :: [[ConstrTerm ()]] -> [[[[ConstrTerm ()]]]]
> matchInductive =
>   map (groupRules . promote) . filter isInductive . transpose .
>     map (matches id)
>   where isInductive = all (not . isVarPattern . fst)

> groupRules :: [(ConstrTerm (),a)] -> [[a]]
> groupRules [] = []
> groupRules ((t,ts):tss) = (ts:map snd same) : groupRules tss
>   where (same,other) = partition ((t ==) . fst) tss

> promote :: [(ConstrTerm (),a)] -> [(ConstrTerm (),a)]
> promote tss = if any (isFloat . fst) tss then map (apFst toFloat) tss else tss
>   where isFloat (LiteralPattern _ l) =
>           case l of
>             Float _ -> True
>             _       -> False
>         isFloat (ConstructorPattern _ _ _) = False
>         toFloat (LiteralPattern a (Int i)) =
>           LiteralPattern a (Float (fromIntegral i))
>         toFloat (LiteralPattern a (Float f)) = LiteralPattern a (Float f)

> matches :: ([ConstrTerm a] -> [ConstrTerm a]) -> [ConstrTerm a]
>         -> [(ConstrTerm a,[ConstrTerm a])]
> matches _ [] = []
> matches f (t:ts) = (t',f (ts' ++ ts)) : matches (f . (t:)) ts
>   where (t',ts') = match t
>         match (ConstructorPattern a c ts) = (ConstructorPattern a c [],ts)
>         match (LiteralPattern a l) = (LiteralPattern a l,[])
>         match (VariablePattern a v) = (VariablePattern a v,[])

\end{verbatim}
Unfortunately, the code has not been desugared yet.
\begin{verbatim}

> desugar :: ConstrTerm a -> ConstrTerm ()
> desugar (LiteralPattern a l) =
>   case l of
>     String cs -> desugar (ListPattern a (map (LiteralPattern a . Char) cs))
>     _ -> LiteralPattern () l
> desugar (NegativePattern a l) = desugar (LiteralPattern a (negateLit l))
>   where negateLit (Int i) = Int (-i)
>         negateLit (Float f) = Float (-f)
> desugar (VariablePattern _ v) = VariablePattern () anonId
> desugar (ConstructorPattern _ c ts) = ConstructorPattern () c (map desugar ts)
> desugar (InfixPattern a t1 op t2) = desugar (ConstructorPattern a op [t1,t2])
> desugar (ParenPattern t) = desugar t
> desugar (TuplePattern ts) = ConstructorPattern () c (map desugar ts)
>   where c = qTupleId (length ts)
> desugar (ListPattern a ts) = desugar (foldr cons nil ts)
>   where nil = ConstructorPattern a qNilId []
>         cons t1 t2 = ConstructorPattern a qConsId [t1,t2]
> desugar (AsPattern _ t) = desugar t
> desugar (LazyPattern t) = VariablePattern () anonId

\end{verbatim}
