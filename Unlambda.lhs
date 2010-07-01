% -*- LaTeX -*-
% $Id: Unlambda.lhs 2970 2010-07-01 09:11:20Z wlux $
%
% Copyright (c) 2007-2010, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Unlambda.lhs}
\section{Naming lambda abstractions}
After simplification and before lifting functions to the top-level,
the compiler assigns explicit names to all lambda abstractions. Each
lambda abstraction $\lambda t_1 \dots t_n \rightarrow e$, which is
still present in the source code, is converted into a let expression
of the form \texttt{let $f\,t_1 \dots t_n = e$ in $f$}, where $f$ is
the canonical name of the lambda expression.
\begin{verbatim}

> module Unlambda(unlambda) where
> import Curry
> import CurryUtils
> import PredefIdent
> import Types
> import Typing

> unlambda :: Module QualType -> Module QualType
> unlambda (Module m es is ds) = Module m es is (map (nameLambdas m) ds)

> class SyntaxTree a where
>   nameLambdas :: ModuleIdent -> a QualType -> a QualType

> instance SyntaxTree TopDecl where
>   nameLambdas _ (DataDecl p cx tc tvs cs clss) = DataDecl p cx tc tvs cs clss
>   nameLambdas _ (NewtypeDecl p cx tc tvs nc clss) =
>     NewtypeDecl p cx tc tvs nc clss
>   nameLambdas _ (TypeDecl p tc tvs ty) = TypeDecl p tc tvs ty
>   nameLambdas m (ClassDecl p cx cls tv ds) =
>     ClassDecl p cx cls tv (map (nameLambdas m) ds)
>   nameLambdas m (InstanceDecl p cx cls ty ds) =
>     InstanceDecl p cx cls ty (map (nameLambdas m) ds)
>   nameLambdas _ (DefaultDecl p tys) = DefaultDecl p tys
>   nameLambdas m (BlockDecl d) = BlockDecl (nameLambdas m d)
>   nameLambdas _ (SplitAnnot p) = SplitAnnot p

> instance SyntaxTree Decl where
>   nameLambdas _ (TypeSig p fs ty) = TypeSig p fs ty
>   nameLambdas m (FunctionDecl p ty f eqs) =
>     FunctionDecl p ty f (map (nameLambdas m) eqs)
>   nameLambdas _ (ForeignDecl p fi ty f ty') = ForeignDecl p fi ty f ty'
>   nameLambdas m (PatternDecl p t rhs) = PatternDecl p t (nameLambdas m rhs)
>   nameLambdas _ (FreeDecl p vs) = FreeDecl p vs

> instance SyntaxTree Equation where
>   nameLambdas m (Equation p lhs rhs) = Equation p lhs (nameLambdas m rhs)

> instance SyntaxTree Rhs where
>   nameLambdas m (SimpleRhs p e _) = SimpleRhs p (nameLambdas m e) []

> instance SyntaxTree Expression where
>   nameLambdas _ (Literal ty l) = Literal ty l
>   nameLambdas _ (Variable ty v) = Variable ty v
>   nameLambdas _ (Constructor ty c) = Constructor ty c
>   nameLambdas m (Apply e1 e2) = Apply (nameLambdas m e1) (nameLambdas m e2)
>   nameLambdas m (Lambda p ts e) =
>     nameLambdas m (Let [funDecl p ty f ts e] (mkVar ty f))
>     where f = lambdaId p
>           ty = qualType (typeOf (Lambda p ts e))
>   nameLambdas m (Let ds e) = Let (map (nameLambdas m) ds) (nameLambdas m e)
>   nameLambdas m (Case e as) = Case (nameLambdas m e) (map (nameLambdas m) as)
>   nameLambdas m (Fcase e as) =
>     Fcase (nameLambdas m e) (map (nameLambdas m) as)

> instance SyntaxTree Alt where
>   nameLambdas m (Alt p t rhs) = Alt p t (nameLambdas m rhs)

\end{verbatim}
