% -*- LaTeX -*-
% $Id: ILLift.lhs 2817 2009-05-06 14:24:56Z wlux $
%
% Copyright (c) 2000-2009, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{ILLift.lhs}
\section{Normalization}
Before the intermediate language code is translated into abstract
machine code, all case and or expressions occurring in argument
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
>   where (e',ds') = runSt (liftExpr e) nameSupply
>         nameSupply = map (qual m . appIdent (name f') (uniqueId f')) [1..]
>           where (m,f') = splitQualIdent f
>         qual m = maybe qualify qualifyWith m
>         appIdent f n i = renameIdent (mkIdent (f ++ "._#app" ++ show i)) n
> liftDecl (ForeignDecl f cc ie ty) = [ForeignDecl f cc ie ty]
> liftDecl SplitAnnot = [SplitAnnot]

> liftExpr :: Expression -> LiftState (Expression,[Decl])
> liftExpr (Literal l) = return (Literal l,[])
> liftExpr (Variable v) = return (Variable v,[])
> liftExpr (Function f n) = return (Function f n,[])
> liftExpr (Constructor c n) = return (Constructor c n,[])
> liftExpr (Apply f e) =
>   do
>     (f',ds) <- liftExpr f
>     (e',ds') <- liftArg e
>     return (Apply f' e',ds ++ ds')
> liftExpr (Case ev e as) =
>   do
>     (e',ds) <- liftExpr e
>     (as',ds') <- mapLift liftAlt as
>     return (Case ev e' as',ds ++ ds')
> liftExpr (Or e1 e2) =
>   do
>     (e1',ds) <- liftExpr e1
>     (e2',ds') <- liftExpr e2
>     return (Or e1' e2',ds ++ ds')
> liftExpr (Exist v e) =
>   do
>     (e',ds) <- liftExpr e
>     return (Exist v e',ds)
> liftExpr (Let b e) =
>   do
>     (b',ds) <- liftBinding b
>     (e',ds') <- liftExpr e
>     return (Let b' e',ds ++ ds')
> liftExpr (Letrec bs e) =
>   do
>     (bs',ds) <- mapLift liftBinding bs
>     (e',ds') <- liftExpr e
>     return (Letrec bs' e',ds ++ ds')
> liftExpr (SrcLoc p e) =
>   do
>     (e',ds) <- liftExpr e
>     return (SrcLoc p e',ds)

> liftArg :: Expression -> LiftState (Expression,[Decl])
> liftArg (Literal l) = return (Literal l,[])
> liftArg (Variable v) = return (Variable v,[])
> liftArg (Function f n) = return (Function f n,[])
> liftArg (Constructor c n) = return (Constructor c n,[])
> liftArg (Apply f e) =
>   do
>     (f',ds) <- liftArg f
>     (e',ds') <- liftArg e
>     return (Apply f' e',ds ++ ds')
> liftArg (Case ev e as) = lift (Case ev e as)
> liftArg (Or e1 e2) = lift (Or e1 e2)
> liftArg (Exist v e) =
>   do
>     (e',ds) <- liftArg e
>     return (Exist v e',ds)
> liftArg (Let b e) =
>   do
>     (b',ds) <- liftBinding b
>     (e',ds') <- liftArg e
>     return (Let b' e',ds ++ ds')
> liftArg (Letrec bs e) =
>   do
>     (bs',ds) <- mapLift liftBinding bs
>     (e',ds') <- liftArg e
>     return (Letrec bs' e',ds ++ ds')
> liftArg (SrcLoc p e) =
>   do
>     (e',ds) <- liftArg e
>     return (SrcLoc p e',ds)

> lift :: Expression -> LiftState (Expression,[Decl])
> lift e =
>   do
>     f <- uniqueName
>     (e',ds') <- liftExpr e
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

> liftAlt :: Alt -> LiftState (Alt,[Decl])
> liftAlt (Alt t e) =
>   do
>     (e',ds) <- liftExpr e
>     return (Alt t e',ds)

> liftBinding :: Binding -> LiftState (Binding,[Decl])
> liftBinding (Binding v e) =
>   do
>     (e',ds) <- liftArg e
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
> fv (Or e1 e2) = fv e1 ++ fv e2
> fv (Exist v e) = filter (v /=) (fv e)
> fv (Let (Binding v e1) e2) = fv e1 ++ filter (v /=) (fv e2)
> fv (Letrec bs e) =
>   filter (`notElem` bvs) ([v | Binding _ e <- bs, v <- fv e] ++ fv e)
>   where bvs = [v | Binding v _ <- bs]
> fv (SrcLoc _ e) = fv e

> fvAlt :: Alt -> [Ident]
> fvAlt (Alt t e) = filter (`notElem` bv t) (fv e)
>   where bv (LiteralPattern _) = []
>         bv (ConstructorPattern _ vs) = vs
>         bv (VariablePattern v) = [v]

\end{verbatim}
