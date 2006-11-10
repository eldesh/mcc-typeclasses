% -*- LaTeX -*-
% $Id: Trust.lhs 1999 2006-11-10 21:53:29Z wlux $
%
% Copyright (c) 2006, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Eval.lhs}
\section{Collecting Trust Annotations}
The module \texttt{Trust} computes the trust annotation environment.
There is no need to check the annotations because this happens already
while checking the definitions of the module.
\begin{verbatim}

> module Trust(trustEnv,trustEnvGoal) where
> import Base
> import Env

\end{verbatim}
The function \texttt{trustEnv} collects the trust attributes from all
trust annotations in the source code. In addition, a default trust
attribute is assigned to all defined functions for which there is no
explicit annotation. By default, local functions inherit the trust
attribute of their enclosing function. The default trust attribute for
global functions is controlled by the \texttt{--trusted} compiler
option. The default trust annotations \verb|{-# TRUST _ #-}| and
\verb|{-# SUSPECT _ #-}| override the inherited attribute for all
declarations without an explicit trust annotation in the same
declaration group. Note that default trust annotations apply to the
right hand sides of pattern declarations, but not to the body of a
declaration group. Thus, in the following, contrived example
\begin{verbatim}
{-# SUSPECT f #-}
f x = let g x = x in h (g z)
  where {-# TRUST _ #-}
        h _ = z
        z = let i y = y in i x
\end{verbatim}
the local functions \texttt{h} and \texttt{i} are trusted, but
\texttt{g} is not.
\begin{verbatim}

> trustEnv :: Trust -> [TopDecl a] -> TrustEnv
> trustEnv tr ds = trust tr [d | BlockDecl d <- ds] emptyEnv

> trustEnvGoal :: Trust -> Goal a -> TrustEnv
> trustEnvGoal tr (Goal _ e ds) = trust tr e (trust tr ds emptyEnv)

> class SyntaxTree a where
>   trust :: Trust -> a -> TrustEnv -> TrustEnv

>   trustList :: Trust -> [a] -> TrustEnv -> TrustEnv
>   trustList tr xs env = foldr (trust tr) env xs

> instance SyntaxTree a => SyntaxTree [a] where
>   trust = trustList

> instance SyntaxTree (Decl a) where
>   trust tr (FunctionDecl _ f eqs) env =
>     case lookupEnv f env of
>       Just tr' -> trust tr' eqs env
>       Nothing -> trust tr eqs (bindEnv f tr env)
>   trust tr (PatternDecl _ _ rhs) env = trust tr rhs env
>   trust _ _ env = env

>   trustList tr ds env = foldr (trust tr') env' ds
>     where tr' = head $ [tr | TrustAnnot _ tr Nothing <- ds] ++ [tr]
>           env' =
>             foldr ($) env
>                   [bindEnv f tr | TrustAnnot _ tr (Just fs) <- ds, f <- fs]

> instance SyntaxTree (Equation a) where
>   trust tr (Equation _ _ rhs) = trust tr rhs

> instance SyntaxTree (Rhs a) where
>   trust tr (SimpleRhs _ e ds) = trust tr e . trust tr ds
>   trust tr (GuardedRhs es ds) = trust tr es . trust tr ds

> instance SyntaxTree (CondExpr a) where
>   trust tr (CondExpr _ g e) = trust tr g . trust tr e

> instance SyntaxTree (Expression a) where
>   trust _ (Literal _ _) = id
>   trust _ (Variable _ _) = id
>   trust _ (Constructor _ _) = id
>   trust tr (Paren e) = trust tr e
>   trust tr (Typed e _) = trust tr e
>   trust tr (Tuple es) = trust tr es
>   trust tr (List _ es) = trust tr es
>   trust tr (ListCompr e qs) = trust tr e . trust tr qs
>   trust tr (EnumFrom e) = trust tr e
>   trust tr (EnumFromThen e1 e2) = trust tr e1 . trust tr e2
>   trust tr (EnumFromTo e1 e2) = trust tr e1 . trust tr e2
>   trust tr (EnumFromThenTo e1 e2 e3) = trust tr e1 . trust tr e2 . trust tr e3
>   trust tr (UnaryMinus e) = trust tr e
>   trust tr (Apply e1 e2) = trust tr e1 . trust tr e2
>   trust tr (InfixApply e1 _ e2) = trust tr e1 . trust tr e2
>   trust tr (LeftSection e _) = trust tr e
>   trust tr (RightSection _ e) = trust tr e
>   trust tr (Lambda _ e) = trust tr e
>   trust tr (Let ds e) = trust tr ds . trust tr e
>   trust tr (Do sts e) = trust tr sts . trust tr e
>   trust tr (IfThenElse e1 e2 e3) = trust tr e1 . trust tr e2 . trust tr e3
>   trust tr (Case e as) = trust tr e . trust tr as

> instance SyntaxTree (Statement a) where
>   trust tr (StmtExpr e) = trust tr e
>   trust tr (StmtDecl ds) = trust tr ds
>   trust tr (StmtBind _ e) = trust tr e

> instance SyntaxTree (Alt a) where
>   trust tr (Alt _ _ rhs) = trust tr rhs

\end{verbatim}
