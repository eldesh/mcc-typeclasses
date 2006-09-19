% -*- LaTeX -*-
% $Id: OverlapCheck.lhs 1913 2006-05-07 13:44:36Z wlux $
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

> overlapCheck :: [Warn] -> Module -> [String]
> overlapCheck v (Module m _ _ ds) =
>   report v $ overlap noPosition [d | BlockDecl d <- ds] []
>   where noPosition = error "noPosition"

> overlapCheckGoal :: [Warn] -> Goal -> [String]
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

> instance Syntax Decl where
>   overlap _ (FunctionDecl p f eqs) =
>     ([P p f | isNonDet eqs] ++) . overlap p eqs
>   overlap _ (PatternDecl p _ rhs) = overlap p rhs
>   overlap _ _ = id

> instance Syntax Equation where
>   overlap _ (Equation p _ rhs) = overlap p rhs

> instance Syntax Rhs where
>   overlap _ (SimpleRhs p e ds) = overlap p ds . overlap p e
>   overlap p (GuardedRhs es ds) = overlap p ds . overlap p es

> instance Syntax CondExpr where
>   overlap _ (CondExpr p g e) = overlap p g . overlap p e

> instance Syntax Expression where
>   overlap _ (Literal _) = id
>   overlap _ (Variable _) = id
>   overlap _ (Constructor _) = id
>   overlap p (Paren e) = overlap p e
>   overlap p (Typed e _) = overlap p e
>   overlap p (Tuple es) = overlap p es
>   overlap p (List es) = overlap p es
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

> instance Syntax Statement where
>   overlap p (StmtExpr e) = overlap p e
>   overlap p (StmtBind _ e) = overlap p e
>   overlap p (StmtDecl ds) = overlap p ds

> instance Syntax Alt where
>   overlap _ (Alt p _ rhs) = overlap p rhs

\end{verbatim}
The code checking whether a function has rules with overlapping
patterns is essentially a simplified version of the pattern matching
algorithm implemented in module \texttt{ILTrans} (see
Sect.~\ref{sec:il-trans}).
\begin{verbatim}

> isNonDet :: [Equation] -> Bool
> isNonDet eqs =
>   isOverlap [map desugar (snd (flatLhs lhs)) | Equation _ lhs _ <- eqs]

> isOverlap :: [[ConstrTerm]] -> Bool
> isOverlap (ts:tss) =
>   not (null tss) &&
>   case matchInductive (ts:tss) of
>      [] -> True
>      tss:_ -> any isOverlap tss

> matchInductive :: [[ConstrTerm]] -> [[[[ConstrTerm]]]]
> matchInductive =
>   map groupRules . filter isInductive . transpose . map (matches id)
>   where isInductive = all (not . isVariablePattern . fst)

> groupRules :: [(ConstrTerm,[ConstrTerm])] -> [[[ConstrTerm]]]
> groupRules [] = []
> groupRules ((t,ts):tss) = (ts:map snd same) : groupRules tss
>   where (same,other) = partition ((t ==) . fst) tss

> matches :: ([ConstrTerm] -> [ConstrTerm]) -> [ConstrTerm]
>         -> [(ConstrTerm,[ConstrTerm])]
> matches _ [] = []
> matches f (t:ts) = (t',f (ts' ++ ts)) : matches (f . (t:)) ts
>   where (t',ts') = match t
>         match (ConstructorPattern c ts) = (ConstructorPattern c [],ts)
>         match (LiteralPattern l) = (LiteralPattern l,[])
>         match (VariablePattern v) = (VariablePattern v,[])

> isVariablePattern :: ConstrTerm -> Bool
> isVariablePattern (LiteralPattern _) = False
> isVariablePattern (ConstructorPattern _ _) = False
> isVariablePattern (VariablePattern _) = True

\end{verbatim}
Unfortunately, the code has not been desugared yet.
\begin{verbatim}

> desugar :: ConstrTerm -> ConstrTerm
> desugar (LiteralPattern l) =
>   case l of
>     String cs -> desugar (ListPattern (map (LiteralPattern . Char) cs))
>     _ -> LiteralPattern l
> desugar (NegativePattern _ l) = desugar (LiteralPattern (negateLit l))
>   where negateLit (Int v i) = Int v (-i)
>         negateLit (Float f) = Float (-f)
> desugar (VariablePattern v) = VariablePattern anonId
> desugar (ConstructorPattern c ts) = ConstructorPattern c (map desugar ts)
> desugar (InfixPattern t1 op t2) = desugar (ConstructorPattern op [t1,t2])
> desugar (ParenPattern t) = desugar t
> desugar (TuplePattern ts) = desugar (ConstructorPattern c ts)
>   where c = qTupleId (length ts)
> desugar (ListPattern ts) = desugar (foldr cons nil ts)
>   where nil = ConstructorPattern qNilId []
>         cons t1 t2 = ConstructorPattern qConsId [t1,t2]
> desugar (AsPattern _ t) = desugar t
> desugar (LazyPattern _) = VariablePattern anonId

\end{verbatim}
