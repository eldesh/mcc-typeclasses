% -*- LaTeX -*-
% $Id: Base.lhs 2515 2007-10-18 10:54:19Z wlux $
%
% Copyright (c) 1999-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Base.lhs}
\section{Common Definitions for the Compiler}
The module \texttt{Base} provides definitions that are commonly used
in various phases of the compiler.
\begin{verbatim}

> module Base where
> import Curry
> import CurryUtils
> import Env
> import List
> import Position
> import Set

\end{verbatim}
\paragraph{Free and bound variables}
The compiler needs to compute the sets of free and bound variables for
various entities. We will devote three type classes to that purpose.
The \texttt{QualExpr} class is expected to take into account that it
is possible to use a qualified name for referring to a function
defined in the current module and therefore \emph{M.x} and $x$, where
$M$ is the current module name, should be considered the same name.
However, note that this is correct only after renaming all local
definitions, as \emph{M.x} always denotes an entity defined at the
top-level.

The \texttt{Decl} instance of \texttt{QualExpr} returns all free
variables on the right hand side, regardless of whether they are bound
on the left hand side. This is more convenient because declarations are
usually processed in a declaration group where the set of free
variables cannot be computed independently for each declaration.
\begin{verbatim}

> class Expr e where
>   fv :: e -> [Ident]
> class QualExpr e where
>   qfv :: ModuleIdent -> e -> [Ident]
> class QuantExpr e where
>   bv :: e -> [Ident]

> instance Expr e => Expr [e] where
>   fv = concat . map fv
> instance QualExpr e => QualExpr [e] where
>   qfv m = concat . map (qfv m)
> instance QuantExpr e => QuantExpr [e] where
>   bv = concat . map bv

> instance QualExpr (TopDecl a) where
>   qfv m (ClassDecl _ _ _ _ ds) = qfv m ds
>   qfv m (InstanceDecl _ _ _ _ ds) = qfv m ds
>   qfv m (BlockDecl d) = qfv m d
>   qfv _ _ = []

> instance QuantExpr (TopDecl a) where
>   bv (ClassDecl _ _ _ _ ds) = [f | TypeSig _ fs _ <- ds, f <- fs]
>   bv (BlockDecl d) = bv d
>   bv _ = []

> instance QualExpr (Decl a) where
>   qfv m (FunctionDecl _ _ eqs) = qfv m eqs
>   qfv m (PatternDecl _ _ rhs) = qfv m rhs
>   qfv _ _ = []

> instance QuantExpr (Decl a) where
>   bv (FunctionDecl _ f _) = [f]
>   bv (ForeignDecl _ _ _ _ f _) = [f]
>   bv (PatternDecl _ t _) = bv t
>   bv (FreeDecl _ vs) = vs
>   bv _ = []

> instance QualExpr (Equation a) where
>   qfv m (Equation _ lhs rhs) = filterBv lhs (qfv m rhs)

> instance QuantExpr (Lhs a) where
>   bv = bv . snd . flatLhs

> instance QualExpr (Rhs a) where
>   qfv m (SimpleRhs _ e ds) = filterBv ds (qfv m e ++ qfv m ds)
>   qfv m (GuardedRhs es ds) = filterBv ds (qfv m es ++ qfv m ds)

> instance QualExpr (CondExpr a) where
>   qfv m (CondExpr _ g e) = qfv m g ++ qfv m e

> instance QualExpr (Expression a) where
>   qfv _ (Literal _ _) = []
>   qfv m (Variable _ v) = maybe [] return (localIdent m v)
>   qfv _ (Constructor _ _) = []
>   qfv m (Paren e) = qfv m e
>   qfv m (Typed e _) = qfv m e
>   qfv m (Tuple es) = qfv m es
>   qfv m (List _ es) = qfv m es
>   qfv m (ListCompr e qs) = foldr (qfvStmt m) (qfv m e) qs
>   qfv m (EnumFrom e) = qfv m e
>   qfv m (EnumFromThen e1 e2) = qfv m e1 ++ qfv m e2
>   qfv m (EnumFromTo e1 e2) = qfv m e1 ++ qfv m e2
>   qfv m (EnumFromThenTo e1 e2 e3) = qfv m e1 ++ qfv m e2 ++ qfv m e3
>   qfv m (UnaryMinus e) = qfv m e
>   qfv m (Apply e1 e2) = qfv m e1 ++ qfv m e2
>   qfv m (InfixApply e1 op e2) = qfv m op ++ qfv m e1 ++ qfv m e2
>   qfv m (LeftSection e op) = qfv m op ++ qfv m e
>   qfv m (RightSection op e) = qfv m op ++ qfv m e
>   qfv m (Lambda _ ts e) = filterBv ts (qfv m e)
>   qfv m (Let ds e) = filterBv ds (qfv m ds ++ qfv m e)
>   qfv m (Do sts e) = foldr (qfvStmt m) (qfv m e) sts
>   qfv m (IfThenElse e1 e2 e3) = qfv m e1 ++ qfv m e2 ++ qfv m e3
>   qfv m (Case e alts) = qfv m e ++ qfv m alts

> qfvStmt :: ModuleIdent -> Statement a -> [Ident] -> [Ident]
> qfvStmt m st fvs = qfv m st ++ filterBv st fvs

> instance QualExpr (Statement a) where
>   qfv m (StmtExpr e) = qfv m e
>   qfv m (StmtBind _ t e) = qfv m e
>   qfv m (StmtDecl ds) = filterBv ds (qfv m ds)

> instance QualExpr (Alt a) where
>   qfv m (Alt _ t rhs) = filterBv t (qfv m rhs)

> instance QuantExpr (Statement a) where
>   bv (StmtExpr e) = []
>   bv (StmtBind _ t e) = bv t
>   bv (StmtDecl ds) = bv ds

> instance QualExpr (InfixOp a) where
>   qfv m op = qfv m (infixOp op)

> instance QuantExpr (ConstrTerm a) where
>   bv (LiteralPattern _ _) = []
>   bv (NegativePattern _ _) = []
>   bv (VariablePattern _ v) = [v | v /= anonId]
>   bv (ConstructorPattern _ _ ts) = bv ts
>   bv (InfixPattern _ t1 _ t2) = bv t1 ++ bv t2
>   bv (ParenPattern t) = bv t
>   bv (TuplePattern ts) = bv ts
>   bv (ListPattern _ ts) = bv ts
>   bv (AsPattern v t) = v : bv t
>   bv (LazyPattern t) = bv t

> instance Expr QualTypeExpr where
>   fv (QualTypeExpr _ ty) = fv ty

> instance Expr ClassAssert where
>   fv (ClassAssert _ ty) = fv ty

> instance Expr TypeExpr where
>   fv (ConstructorType _) = []
>   fv (VariableType tv) = [tv]
>   fv (TupleType tys) = fv tys
>   fv (ListType ty) = fv ty
>   fv (ArrowType ty1 ty2) = fv ty1 ++ fv ty2
>   fv (ApplyType ty1 ty2) = fv ty1 ++ fv ty2

> filterBv :: QuantExpr e => e -> [Ident] -> [Ident]
> filterBv e = filter (`notElemSet` fromListSet (bv e))

\end{verbatim}
\paragraph{Miscellany}
Error handling
\begin{verbatim}

> errorAt :: Monad m => Position -> String -> m a
> errorAt p msg = fail (atP p msg)

> internalError :: String -> a
> internalError what = error ("internal error: " ++ what)

\end{verbatim}
Name supply for the generation of (type) variable names.
\begin{verbatim}

> nameSupply :: [Ident]
> nameSupply = map mkIdent [c:showNum i | i <- [0..], c <- ['a'..'z']]
>   where showNum 0 = ""
>         showNum n = show n

\end{verbatim}
\ToDo{The \texttt{nameSupply} should respect the current case mode, 
i.e., use upper case for variables in Prolog mode.}

The function \texttt{duplicates} returns a list containing all
duplicate items from its input list. The result is a list of pairs
whose first element contains the first occurrence of a duplicate item
and whose second element contains a list of all remaining occurrences
of that item.
\begin{verbatim}

> duplicates :: Eq a => [a] -> [(a,[a])]
> duplicates [] = []
> duplicates (x:xs)
>   | null ys = duplicates xs
>   | otherwise = (x,ys) : duplicates zs
>   where (ys,zs) = partition (x ==) xs

\end{verbatim}
