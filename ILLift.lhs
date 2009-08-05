% -*- LaTeX -*-
% $Id: ILLift.lhs 2889 2009-08-05 15:57:07Z wlux $
%
% Copyright (c) 2000-2009, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{ILLift.lhs}
\section{Normalization}
Before the intermediate language code is translated into abstract
machine code, all (f)case and choice expressions occurring in argument
positions are lifted into global functions.
\begin{verbatim}

> module ILLift(liftProg) where
> import Combined
> import IL
> import List
> import Monad
> import Utils

> type LiftState a = St [QualIdent] a

> liftProg :: Module -> Module
> liftProg (Module m is ds) = Module m is (concatMap liftDecl ds)

> liftDecl :: Decl -> [Decl]
> liftDecl (DataDecl tc n cs) = [DataDecl tc n cs]
> liftDecl (TypeDecl tc n ty) = [TypeDecl tc n ty]
> liftDecl (FunctionDecl f vs ty e) = FunctionDecl f vs ty e' : ds'
>   where (e',ds') = runSt (liftExpr True e) nameSupply
>         nameSupply = map (qual m . appIdent (name f') (uniqueId f')) [1..]
>           where (m,f') = splitQualIdent f
>         qual m = maybe qualify qualifyWith m
>         appIdent f n i = renameIdent (mkIdent (f ++ "._#app" ++ show i)) n
> liftDecl (ForeignDecl f cc ie ty) = [ForeignDecl f cc ie ty]
> liftDecl SplitAnnot = [SplitAnnot]

> liftExpr :: Bool -> Expression -> LiftState (Expression,[Decl])
> liftExpr _ (Literal l) = return (Literal l,[])
> liftExpr _ (Variable v) = return (Variable v,[])
> liftExpr _ (Function f n) = return (Function f n,[])
> liftExpr _ (Constructor c n) = return (Constructor c n,[])
> liftExpr root (Apply f e) =
>   do
>     (f',ds) <- liftExpr root f
>     (e',ds') <- liftExpr False e
>     return (Apply f' e',ds ++ ds')
> liftExpr root (Case ev e as)
>   | root =
>       do
>         (e',ds) <- liftExpr root e
>         (as',ds') <- mapLift (liftAlt root) as
>         return (Case ev e' as',ds ++ ds')
>   | otherwise = lift (Case ev e as)
> liftExpr root (Choice es)
>   | root =
>       do
>         (es',ds) <- mapLift (liftExpr root) es
>         return (Choice es',ds)
>   | otherwise = lift (Choice es)
> liftExpr root (Exist vs e) =
>   do
>     (e',ds) <- liftExpr root e
>     return (Exist vs e',ds)
> liftExpr root (Let rec bs e) =
>   do
>     (bs',ds) <- mapLift liftBinding bs
>     (e',ds') <- liftExpr root e
>     return (Let rec bs' e',ds ++ ds')
> liftExpr root (SrcLoc p e) =
>   do
>     (e',ds) <- liftExpr root e
>     return (SrcLoc p e',ds)

> lift :: Expression -> LiftState (Expression,[Decl])
> lift e =
>   do
>     f <- uniqueName
>     (e',ds') <- liftExpr True e
>     return (foldl Apply (Function f n) (map Variable fvs),
>             FunctionDecl f fvs ty e' : ds')
>   where fvs = nub (fv e)
>         n = length fvs
>         ty = foldr1 TypeArrow (map TypeVariable [0..n])

\end{verbatim}
\ToDo{The type of lifted functions is too general ($\forall
  \alpha_1\dots\alpha_{n+1} . \alpha_1 \rightarrow \dots \rightarrow
  \alpha_n \rightarrow \alpha_{n+1}$, where $n$ is the arity of the
  function). In order to fix this bug we need more type information in
  the intermediate language so that we can compute the type of any
  expression in the module.}
\begin{verbatim}

> liftAlt :: Bool -> Alt -> LiftState (Alt,[Decl])
> liftAlt root (Alt t e) =
>   do
>     (e',ds) <- liftExpr root e
>     return (Alt t e',ds)

> liftBinding :: Binding -> LiftState (Binding,[Decl])
> liftBinding (Binding v e) =
>   do
>     (e',ds) <- liftExpr False e
>     return (Binding v e',ds)

> mapLift :: (a -> LiftState (a,[Decl])) -> [a] -> LiftState ([a],[Decl])
> mapLift f xs = liftM (apSnd concat . unzip) (mapM f xs)

> uniqueName :: LiftState QualIdent
> uniqueName = liftM head (updateSt tail)

> fv :: Expression -> [Ident]
> fv (Literal _) = []
> fv (Variable v) = [v]
> fv (Function _ _) = []
> fv (Constructor _ _) = []
> fv (Apply f e) = fv f ++ fv e
> fv (Case _ e as) = fv e ++ concatMap fvAlt as
> fv (Choice es) = concatMap fv es
> fv (Exist vs e) = filter (`notElem` vs) (fv e)
> fv (Let rec bs e) =
>   fvBinds rec vs (concatMap fv es) ++ filter (`notElem` vs) (fv e)
>   where (vs,es) = unzip [(v,e) | Binding v e <- bs]
>         fvBinds NonRec _ = id
>         fvBinds Rec vs = filter (`notElem` vs)
> fv (SrcLoc _ e) = fv e

> fvAlt :: Alt -> [Ident]
> fvAlt (Alt t e) = filter (`notElem` bv t) (fv e)
>   where bv (LiteralPattern _) = []
>         bv (ConstructorPattern _ vs) = vs
>         bv (VariablePattern v) = [v]

\end{verbatim}
