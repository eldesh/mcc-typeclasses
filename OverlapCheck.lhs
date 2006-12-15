% -*- LaTeX -*-
% $Id: OverlapCheck.lhs 2046 2006-12-15 13:29:51Z wlux $
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
> import Typing

> overlapCheck :: [Warn] -> Module Type -> [String]
> overlapCheck v (Module m _ _ ds) = report v $ overlap noPosition ds []
>   where noPosition = error "noPosition"

> overlapCheckGoal :: [Warn] -> Goal Type -> [String]
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

> instance Typeable a => Syntax (TopDecl a) where
>   overlap _ (ClassDecl p _ _ _ ds) = overlap p ds 
>   overlap _ (InstanceDecl p _ _ _ ds) = overlap p ds 
>   overlap p (BlockDecl d) = overlap p d
>   overlap _ _ = id

> instance Typeable a => Syntax (MethodDecl a) where
>   overlap _ (MethodFixity _ _ _ _) = id
>   overlap _ (MethodSig _ _ _) = id
>   overlap _ (MethodDecl p f eqs) = ([P p f | isNonDet eqs] ++) . overlap p eqs

> instance Typeable a => Syntax (Decl a) where
>   overlap _ (FunctionDecl p f eqs) =
>     ([P p f | isNonDet eqs] ++) . overlap p eqs
>   overlap _ (PatternDecl p _ rhs) = overlap p rhs
>   overlap _ _ = id

> instance Typeable a => Syntax (Equation a) where
>   overlap _ (Equation p _ rhs) = overlap p rhs

> instance Typeable a => Syntax (Rhs a) where
>   overlap _ (SimpleRhs p e ds) = overlap p ds . overlap p e
>   overlap p (GuardedRhs es ds) = overlap p ds . overlap p es

> instance Typeable a => Syntax (CondExpr a) where
>   overlap _ (CondExpr p g e) = overlap p g . overlap p e

> instance Typeable a => Syntax (Expression a) where
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
>   overlap p (Lambda _ e) = overlap p e
>   overlap p (Let ds e) = overlap p ds . overlap p e
>   overlap p (Do sts e) = overlap p sts . overlap p e
>   overlap p (IfThenElse e1 e2 e3) =
>     overlap p e1 . overlap p e2 . overlap p e3
>   overlap p (Case e as) = overlap p e . overlap p as

> instance Typeable a => Syntax (Statement a) where
>   overlap p (StmtExpr e) = overlap p e
>   overlap p (StmtBind _ e) = overlap p e
>   overlap p (StmtDecl ds) = overlap p ds

> instance Typeable a => Syntax (Alt a) where
>   overlap _ (Alt p _ rhs) = overlap p rhs

\end{verbatim}
The code checking whether a function has rules with overlapping
patterns is essentially a simplified version of the pattern matching
algorithm implemented in module \texttt{ILTrans} (see
Sect.~\ref{sec:il-trans}).
\begin{verbatim}

> isNonDet :: Typeable a => [Equation a] -> Bool
> isNonDet eqs =
>   isOverlap [map desugar (snd (flatLhs lhs)) | Equation _ lhs _ <- eqs]

> isOverlap :: [[ConstrTerm Type]] -> Bool
> isOverlap (ts:tss) =
>   not (null tss) &&
>   case matchInductive (ts:tss) of
>      [] -> True
>      tss:_ -> any isOverlap tss

> matchInductive :: [[ConstrTerm Type]] -> [[[[ConstrTerm Type]]]]
> matchInductive =
>   map groupRules . filter isInductive . transpose . map (matches id)
>   where isInductive = all (not . isVariablePattern . fst)

> groupRules :: [(ConstrTerm Type,[ConstrTerm Type])] -> [[[ConstrTerm Type]]]
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

> desugar :: Typeable a => ConstrTerm a -> ConstrTerm Type
> desugar (LiteralPattern a l) =
>   case l of
>     Char _ -> LiteralPattern ty l
>     Int i -> LiteralPattern ty (fixLiteral ty i)
>       where fixLiteral (TypeConstrained tys _) = fixLiteral (head tys)
>             fixLiteral ty
>               | ty == intType = Int
>               | ty == floatType = Float . fromIntegral
>               | otherwise = internalError "desugar"
>     Float _ -> LiteralPattern ty l 
>     String cs ->
>       desugar (ListPattern ty (map (LiteralPattern charType . Char) cs))
>   where ty = typeOf a
> desugar (NegativePattern a l) = desugar (LiteralPattern a (negateLit l))
>   where negateLit (Int i) = Int (-i)
>         negateLit (Float f) = Float (-f)
> desugar (VariablePattern a v) = VariablePattern (typeOf a) anonId
> desugar (ConstructorPattern a c ts) =
>   ConstructorPattern (typeOf a) c (map desugar ts)
> desugar (InfixPattern a t1 op t2) =
>   desugar (ConstructorPattern a op [t1,t2])
> desugar (ParenPattern t) = desugar t
> desugar (TuplePattern ts) = ConstructorPattern ty c (map desugar ts)
>   where c = qTupleId (length ts)
>         ty = tupleType (map typeOf ts)
> desugar (ListPattern a ts) = desugar (foldr cons nil ts)
>   where nil = ConstructorPattern a qNilId []
>         cons t1 t2 = ConstructorPattern a qConsId [t1,t2]
> desugar (AsPattern _ t) = desugar t
> desugar (LazyPattern t) = VariablePattern (typeOf t) anonId

\end{verbatim}
