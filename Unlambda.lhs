% -*- LaTeX -*-
% $Id: Unlambda.lhs 2968 2010-06-24 14:39:50Z wlux $
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
the canonical name of the lambda expression, and the type of the
lambda abstraction is recorded in the type environment.
\begin{verbatim}

> module Unlambda(unlambda) where
> import Combined
> import Curry
> import CurryUtils
> import Monad
> import PredefIdent
> import TopEnv
> import Types
> import Typing
> import ValueInfo

> type UnlambdaState a = StateT ValueEnv Id a

> unlambda :: ValueEnv -> Module Type -> (Module Type,ValueEnv)
> unlambda tyEnv (Module m es is ds) = runSt doUnlambda tyEnv
>   where doUnlambda =
>           do
>             ds' <- mapM (nameLambdas m) ds
>             tyEnv' <- fetchSt
>             return (Module m es is ds',tyEnv')

> class SyntaxTree a where
>   nameLambdas :: ModuleIdent -> a Type -> UnlambdaState (a Type)

> instance SyntaxTree TopDecl where
>   nameLambdas _ (DataDecl p cx tc tvs cs clss) =
>      return (DataDecl p cx tc tvs cs clss)
>   nameLambdas _ (NewtypeDecl p cx tc tvs nc clss) =
>      return (NewtypeDecl p cx tc tvs nc clss)
>   nameLambdas _ (TypeDecl p tc tvs ty) = return (TypeDecl p tc tvs ty)
>   nameLambdas m (ClassDecl p cx cls tv ds) =
>     liftM (ClassDecl p cx cls tv) (mapM (nameLambdas m) ds)
>   nameLambdas m (InstanceDecl p cx cls ty ds) =
>     liftM (InstanceDecl p cx cls ty) (mapM (nameLambdas m) ds)
>   nameLambdas _ (DefaultDecl p tys) = return (DefaultDecl p tys)
>   nameLambdas m (BlockDecl d) = liftM BlockDecl (nameLambdas m d)
>   nameLambdas _ (SplitAnnot p) = return (SplitAnnot p)

> instance SyntaxTree Decl where
>   nameLambdas _ (TypeSig p fs ty) = return (TypeSig p fs ty)
>   nameLambdas m (FunctionDecl p ty f eqs) =
>     liftM (FunctionDecl p ty f) (mapM (nameLambdas m) eqs)
>   nameLambdas _ (ForeignDecl p fi ty f ty') =
>     return (ForeignDecl p fi ty f ty')
>   nameLambdas m (PatternDecl p t rhs) =
>     liftM (PatternDecl p t) (nameLambdas m rhs)
>   nameLambdas _ (FreeDecl p vs) = return (FreeDecl p vs)

> instance SyntaxTree Equation where
>   nameLambdas m (Equation p lhs rhs) =
>     liftM (Equation p lhs) (nameLambdas m rhs)

> instance SyntaxTree Rhs where
>   nameLambdas m (SimpleRhs p e _) =
>     liftM (flip (SimpleRhs p) []) (nameLambdas m e)

> instance SyntaxTree Expression where
>   nameLambdas _ (Literal ty l) = return (Literal ty l)
>   nameLambdas _ (Variable ty v) = return (Variable ty v)
>   nameLambdas _ (Constructor ty c) = return (Constructor ty c)
>   nameLambdas m (Apply e1 e2) =
>     liftM2 Apply (nameLambdas m e1) (nameLambdas m e2)
>   nameLambdas m (Lambda p ts e) =
>     do
>       updateSt_ (bindLambda m f (length ts) ty)
>       nameLambdas m (Let [funDecl p ty f ts e] (mkVar ty f))
>     where f = lambdaId p
>           ty = typeOf (Lambda p ts e)
>           bindLambda m f n ty tyEnv
>             | null (lookupTopEnv f tyEnv) = bindFun m f n (polyType ty) tyEnv
>             | otherwise = tyEnv
>   nameLambdas m (Let ds e) =
>     liftM2 Let (mapM (nameLambdas m) ds) (nameLambdas m e)
>   nameLambdas m (Case e as) =
>     liftM2 Case (nameLambdas m e) (mapM (nameLambdas m) as)
>   nameLambdas m (Fcase e as) =
>     liftM2 Fcase (nameLambdas m e) (mapM (nameLambdas m) as)

> instance SyntaxTree Alt where
>   nameLambdas m (Alt p t rhs) = liftM (Alt p t) (nameLambdas m rhs)

\end{verbatim}
