% -*- LaTeX -*-
% $Id: ILLift.lhs 1817 2005-11-06 23:42:07Z wlux $
%
% Copyright (c) 2000-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{ILLift.lhs}
\section{Normalization}
Before the intermediate language code is translated into abstract
machine code, all complex expressions in argument positions -- i.e.,
everything which is not a constant, variable, function, or application
-- are lifted into global functions.
\begin{verbatim}

> module ILLift where
> import IL
> import Ident
> import Combined
> import List
> import Maybe
> import Monad
> import Utils

> type LiftState a = St [QualIdent] a

> liftProg :: Module -> Module
> liftProg (Module m is ds) =
>   Module m is (concat (runSt (mapM lift ds) nameSupply))
>   where nameSupply =
>           [qualifyWith m (mkIdent ("_app#" ++ (show i))) | i <- [1..]]

> lift :: Decl -> LiftState [Decl]
> lift (DataDecl tc n cs) = return [DataDecl tc n cs]
> lift (TypeDecl tc n ty) = return [TypeDecl tc n ty]
> lift (FunctionDecl f vs ty e) =
>   do
>     (e',ds') <- liftExpr e
>     return (FunctionDecl f vs ty e' : ds')
> lift (ForeignDecl f cc ie ty) = return [ForeignDecl f cc ie ty]

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
> liftExpr (Case ev e alts) =
>   do
>     (e',ds) <- liftExpr e
>     (alts',ds') <- mapLift liftAlt alts
>     return (Case ev e' alts',ds ++ ds')
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
> liftArg e =
>   do
>     f <- uniqueName
>     ds <- lift (FunctionDecl f fvs ty e)
>     return (foldl Apply (Function f (length fvs)) (map Variable fvs),ds)
>   where fvs = nub (fv e)
>         ty = foldr1 TypeArrow $ map TypeVariable $ [0 .. length fvs]

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
> fv (Case _ e alts) = fv e ++ concatMap fvAlt alts
>   where fvAlt (Alt t e) = filter (`notElem` bv t) (fv e)
>         bv (LiteralPattern _) = []
>         bv (ConstructorPattern _ vs) = vs
>         bv (VariablePattern v) = [v]
> fv (Or e1 e2) = fv e1 ++ fv e2
> fv (Exist v e) = filter (v /=) (fv e)
> fv (Let (Binding v e1) e2) = fv e1 ++ filter (v /=) (fv e2)
> fv (Letrec bs e) =
>   filter (`notElem` bvs) ([v | Binding _ e <- bs, v <- fv e] ++ fv e)
>   where bvs = [v | Binding v _ <- bs]

> normalize :: Type -> Type
> normalize ty = rename (nub (tv ty)) ty
>   where rename tvs (TypeConstructor c tys) =
>           TypeConstructor c (map (rename tvs) tys)
>         rename tvs (TypeVariable tv) =
>           TypeVariable (fromJust (elemIndex tv tvs))
>         rename tvs (TypeArrow ty1 ty2) =
>           TypeArrow (rename tvs ty1) (rename tvs ty2)

> tv :: Type -> [Int]
> tv (TypeConstructor _ tys) = concatMap tv tys
> tv (TypeVariable tv) = [tv]
> tv (TypeArrow ty1 ty2) = tv ty1 ++ tv ty2

\end{verbatim}
