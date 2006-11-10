% -*- LaTeX -*-
% $Id: OverlapCheck.lhs 1995 2006-11-10 14:27:14Z wlux $
%
% Copyright (c) 2006, Wolfgang Lux
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
> import List
> import Options

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
>   overlap _ (InstanceDecl p _ _ ds) = overlap p ds 
>   overlap p (BlockDecl d) = overlap p d
>   overlap _ _ = id

> instance Syntax (MethodDecl a) where
>   overlap _ (MethodDecl p f eqs) = ([P p f | isNonDet eqs] ++) . overlap p eqs

> instance Syntax (Decl a) where
>   overlap _ (FunctionDecl p f eqs) =
>     ([P p f | isNonDet eqs] ++) . overlap p eqs
>   overlap _ (PatternDecl p _ rhs) = overlap p rhs
>   overlap _ _ = id

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
>   overlap p (UnaryMinus _ e) = overlap p e
>   overlap p (Apply e1 e2) = overlap p e1 . overlap p e2
>   overlap p (InfixApply e1 _ e2) = overlap p e1 . overlap p e2
>   overlap p (LeftSection e _) = overlap p e
>   overlap p (RightSection _ e) = overlap p e
>   overlap p (Lambda _ e) = overlap p e
>   overlap p (Let ds e) = overlap p ds . overlap p e
>   overlap p (Do sts e) = overlap p sts . overlap p e
>   overlap p (IfThenElse e1 e2 e3) =
>     overlap p e1 . overlap p e2 . overlap p e3
>   overlap p (Case e as) = overlap p e . overlap p as

> instance Syntax (Statement a) where
>   overlap p (StmtExpr e) = overlap p e
>   overlap p (StmtBind _ e) = overlap p e
>   overlap p (StmtDecl ds) = overlap p ds

> instance Syntax (Alt a) where
>   overlap _ (Alt p _ rhs) = overlap p rhs

\end{verbatim}
The code checking whether a function has rules with overlapping
patterns is essentially a simplified version of the pattern matching
algorithm implemented in module \texttt{ILTrans} (see
Sect.~\ref{sec:il-trans}).
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
>   map groupRules . filter isInductive . transpose . map (matches id)
>   where isInductive = all (not . isVariablePattern . fst)

> groupRules :: [(ConstrTerm (),[ConstrTerm ()])] -> [[[ConstrTerm ()]]]
> groupRules [] = []
> groupRules ((t,ts):tss) = (ts:map snd same) : groupRules tss
>   where (same,other) = partition ((t ==) . fst) tss

> matches :: ([ConstrTerm a] -> [ConstrTerm a]) -> [ConstrTerm a]
>         -> [(ConstrTerm a,[ConstrTerm a])]
> matches _ [] = []
> matches f (t:ts) = (t',f (ts' ++ ts)) : matches (f . (t:)) ts
>   where (t',ts') = match t
>         match (ConstructorPattern a c ts) = (ConstructorPattern a c [],ts)
>         match (LiteralPattern a l) = (LiteralPattern a l,[])
>         match (VariablePattern a v) = (VariablePattern a v,[])

> isVariablePattern :: ConstrTerm a -> Bool
> isVariablePattern (LiteralPattern _ _) = False
> isVariablePattern (ConstructorPattern _ _ _) = False
> isVariablePattern (VariablePattern _ _) = True

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
> desugar (TuplePattern ts) = desugar (ConstructorPattern undefined c ts)
>   where c = qTupleId (length ts)
> desugar (ListPattern a ts) = desugar (foldr cons nil ts)
>   where nil = ConstructorPattern a qNilId []
>         cons t1 t2 = ConstructorPattern a qConsId [t1,t2]
> desugar (AsPattern _ t) = desugar t
> desugar (LazyPattern t) = VariablePattern () anonId

\end{verbatim}
