% -*- LaTeX -*-
% $Id: Qual.lhs 1986 2006-10-29 16:45:56Z wlux $
%
% Copyright (c) 2001-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Qual.lhs}
\section{Proper Qualification}
After checking the module and before starting the translation into the
intermediate language, the compiler properly qualifies all
constructors and (global) functions occurring in a pattern or
expression such that their module prefix matches the module of their
definition. This is done also for functions and constructors declared
in the current module. Only functions and variables declared in local
declarations groups as well as function arguments remain unchanged.
\begin{verbatim}

> module Qual(qual,qualGoal) where
> import Base
> import TopEnv

> qual :: ValueEnv -> [TopDecl a] -> [TopDecl a]
> qual tyEnv ds = map (qualTopDecl tyEnv) ds

> qualGoal :: ValueEnv -> Goal a -> Goal a
> qualGoal tyEnv (Goal p e ds) =
>   Goal p (qualExpr tyEnv e) (map (qualDecl tyEnv) ds)

> qualTopDecl :: ValueEnv -> TopDecl a -> TopDecl a
> qualTopDecl tyEnv (BlockDecl d) = BlockDecl (qualDecl tyEnv d)
> qualTopDecl _ d = d

> qualDecl :: ValueEnv -> Decl a -> Decl a
> qualDecl tyEnv (FunctionDecl p f eqs) =
>   FunctionDecl p f (map (qualEqn tyEnv) eqs)
> qualDecl tyEnv (PatternDecl p t rhs) =
>   PatternDecl p (qualTerm tyEnv t) (qualRhs tyEnv rhs)
> qualDecl _ d = d

> qualEqn :: ValueEnv -> Equation a -> Equation a
> qualEqn tyEnv (Equation p lhs rhs) =
>   Equation p (qualLhs tyEnv lhs) (qualRhs tyEnv rhs)

> qualLhs :: ValueEnv -> Lhs a -> Lhs a
> qualLhs tyEnv (FunLhs f ts) = FunLhs f (map (qualTerm tyEnv) ts)
> qualLhs tyEnv (OpLhs t1 op t2) =
>   OpLhs (qualTerm tyEnv t1) op (qualTerm tyEnv t2)
> qualLhs tyEnv (ApLhs lhs ts) =
>   ApLhs (qualLhs tyEnv lhs) (map (qualTerm tyEnv) ts)

> qualTerm :: ValueEnv -> ConstrTerm a -> ConstrTerm a
> qualTerm _ (LiteralPattern a l) = LiteralPattern a l
> qualTerm _ (NegativePattern a l) = NegativePattern a l
> qualTerm _ (VariablePattern a v) = VariablePattern a v
> qualTerm tyEnv (ConstructorPattern a c ts) =
>   ConstructorPattern a (qualIdent tyEnv c) (map (qualTerm tyEnv) ts)
> qualTerm tyEnv (InfixPattern a t1 op t2) =
>   InfixPattern a (qualTerm tyEnv t1) (qualIdent tyEnv op) (qualTerm tyEnv t2)
> qualTerm tyEnv (ParenPattern t) = ParenPattern (qualTerm tyEnv t)
> qualTerm tyEnv (TuplePattern ts) = TuplePattern (map (qualTerm tyEnv) ts)
> qualTerm tyEnv (ListPattern a ts) = ListPattern a (map (qualTerm tyEnv) ts)
> qualTerm tyEnv (AsPattern v t) = AsPattern v (qualTerm tyEnv t)
> qualTerm tyEnv (LazyPattern t) = LazyPattern (qualTerm tyEnv t)

> qualRhs :: ValueEnv -> Rhs a -> Rhs a
> qualRhs tyEnv (SimpleRhs p e ds) =
>   SimpleRhs p (qualExpr tyEnv e) (map (qualDecl tyEnv) ds) 
> qualRhs tyEnv (GuardedRhs es ds) =
>   GuardedRhs (map (qualCondExpr tyEnv) es) (map (qualDecl tyEnv) ds)

> qualCondExpr :: ValueEnv -> CondExpr a -> CondExpr a
> qualCondExpr tyEnv (CondExpr p g e) =
>   CondExpr p (qualExpr tyEnv g) (qualExpr tyEnv e)

> qualExpr :: ValueEnv -> Expression a -> Expression a
> qualExpr _ (Literal a l) = Literal a l
> qualExpr tyEnv (Variable a v) = Variable a (qualIdent tyEnv v)
> qualExpr tyEnv (Constructor a c) = Constructor a (qualIdent tyEnv c)
> qualExpr tyEnv (Paren e) = Paren (qualExpr tyEnv e)
> qualExpr tyEnv (Typed e ty) = Typed (qualExpr tyEnv e) ty
> qualExpr tyEnv (Tuple es) = Tuple (map (qualExpr tyEnv) es)
> qualExpr tyEnv (List a es) = List a (map (qualExpr tyEnv) es)
> qualExpr tyEnv (ListCompr e qs) =
>   ListCompr (qualExpr tyEnv e) (map (qualStmt tyEnv) qs)
> qualExpr tyEnv (EnumFrom e) = EnumFrom (qualExpr tyEnv e)
> qualExpr tyEnv (EnumFromThen e1 e2) =
>   EnumFromThen (qualExpr tyEnv e1) (qualExpr tyEnv e2)
> qualExpr tyEnv (EnumFromTo e1 e2) =
>   EnumFromTo (qualExpr tyEnv e1) (qualExpr tyEnv e2)
> qualExpr tyEnv (EnumFromThenTo e1 e2 e3) =
>   EnumFromThenTo (qualExpr tyEnv e1) (qualExpr tyEnv e2) (qualExpr tyEnv e3)
> qualExpr tyEnv (UnaryMinus op e) = UnaryMinus op (qualExpr tyEnv e)
> qualExpr tyEnv (Apply e1 e2) = Apply (qualExpr tyEnv e1) (qualExpr tyEnv e2)
> qualExpr tyEnv (InfixApply e1 op e2) =
>   InfixApply (qualExpr tyEnv e1) (qualOp tyEnv op) (qualExpr tyEnv e2)
> qualExpr tyEnv (LeftSection e op) =
>   LeftSection (qualExpr tyEnv e) (qualOp tyEnv op)
> qualExpr tyEnv (RightSection op e) =
>   RightSection (qualOp tyEnv op) (qualExpr tyEnv e)
> qualExpr tyEnv (Lambda ts e) =
>   Lambda (map (qualTerm tyEnv) ts) (qualExpr tyEnv e)
> qualExpr tyEnv (Let ds e) = Let (map (qualDecl tyEnv) ds) (qualExpr tyEnv e)
> qualExpr tyEnv (Do sts e) = Do (map (qualStmt tyEnv) sts) (qualExpr tyEnv e)
> qualExpr tyEnv (IfThenElse e1 e2 e3) =
>   IfThenElse (qualExpr tyEnv e1) (qualExpr tyEnv e2) (qualExpr tyEnv e3)
> qualExpr tyEnv (Case e alts) =
>   Case (qualExpr tyEnv e) (map (qualAlt tyEnv) alts)

> qualStmt :: ValueEnv -> Statement a -> Statement a
> qualStmt tyEnv (StmtExpr e) = StmtExpr (qualExpr tyEnv e)
> qualStmt tyEnv (StmtBind t e) =
>   StmtBind (qualTerm tyEnv t) (qualExpr tyEnv e)
> qualStmt tyEnv (StmtDecl ds) = StmtDecl (map (qualDecl tyEnv) ds)

> qualAlt :: ValueEnv -> Alt a -> Alt a
> qualAlt tyEnv (Alt p t rhs) = Alt p (qualTerm tyEnv t) (qualRhs tyEnv rhs)

> qualOp :: ValueEnv -> InfixOp a -> InfixOp a
> qualOp tyEnv (InfixOp a op) = InfixOp a (qualIdent tyEnv op)
> qualOp tyEnv (InfixConstr a op) = InfixConstr a (qualIdent tyEnv op)

> qualIdent :: ValueEnv -> QualIdent -> QualIdent
> qualIdent tyEnv x
>   | isRenamed (unqualify x) = x
>   | otherwise =
>       case qualLookupTopEnv x tyEnv of
>         [y] -> origName y
>         _ -> internalError ("qualIdent: " ++ show x)

\end{verbatim}
