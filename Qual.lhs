% -*- LaTeX -*-
% $Id: Qual.lhs 2022 2006-11-27 18:26:02Z wlux $
%
% Copyright (c) 2001-2006, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Qual.lhs}
\section{Proper Qualification}
After checking the module and before starting the translation into the
intermediate language, the compiler properly qualifies all (type)
constructors and functions occurring in (type) expressions and
patterns so that their module prefix matches the module of their
definition. This is done also for functions and (type) constructors
declared in the current module. The names of local variables and
functions remain unchanged.
\begin{verbatim}

> module Qual(Qual(..)) where
> import Base
> import TopEnv

> class Qual a where
>   qual :: TCEnv -> ValueEnv -> a -> a

> instance Qual a => Qual [a] where
>   qual tcEnv tyEnv = map (qual tcEnv tyEnv)

> instance Qual (Goal a) where
>   qual tcEnv tyEnv (Goal p e ds) =
>     Goal p (qual tcEnv tyEnv e) (qual tcEnv tyEnv ds)

> instance Qual (TopDecl a) where
>   qual tcEnv tyEnv (DataDecl p tc tvs cs) =
>     DataDecl p tc tvs (qual tcEnv tyEnv cs)
>   qual tcEnv tyEnv (NewtypeDecl p tc tvs nc) =
>     NewtypeDecl p tc tvs (qual tcEnv tyEnv nc)
>   qual tcEnv tyEnv (TypeDecl p tc tvs ty) =
>     TypeDecl p tc tvs (qual tcEnv tyEnv ty)
>   qual tcEnv tyEnv (ClassDecl p cx cls tv ds) =
>     ClassDecl p (qual tcEnv tyEnv cx) cls tv (qual tcEnv tyEnv ds)
>   qual tcEnv tyEnv (InstanceDecl p cx cls ty ds) =
>     InstanceDecl p (qual tcEnv tyEnv cx)
>                  (qualIdent tcEnv cls)
>                  (qual tcEnv tyEnv ty)
>                  (qual tcEnv tyEnv ds)
>   qual tcEnv tyEnv (BlockDecl d) = BlockDecl (qual tcEnv tyEnv d)

> instance Qual ConstrDecl where
>   qual tcEnv tyEnv (ConstrDecl p evs c tys) =
>     ConstrDecl p evs c (qual tcEnv tyEnv tys)
>   qual tcEnv tyEnv (ConOpDecl p evs ty1 op ty2) =
>     ConOpDecl p evs (qual tcEnv tyEnv ty1) op (qual tcEnv tyEnv ty2)

> instance Qual NewConstrDecl where
>   qual tcEnv tyEnv (NewConstrDecl p c ty) =
>     NewConstrDecl p c (qual tcEnv tyEnv ty)

> instance Qual QualTypeExpr where
>   qual tcEnv tyEnv (QualTypeExpr cx ty) =
>     QualTypeExpr (qual tcEnv tyEnv cx) (qual tcEnv tyEnv ty)

> instance Qual ClassAssert where
>   qual tcEnv _ (ClassAssert cls tv) = ClassAssert (qualIdent tcEnv cls) tv

> instance Qual TypeExpr where
>   qual tcEnv tyEnv (ConstructorType c tys) =
>     ConstructorType (qualIdent tcEnv c) (qual tcEnv tyEnv tys)
>   qual _ _ (VariableType tv) = VariableType tv
>   qual tcEnv tyEnv (TupleType tys) = TupleType (qual tcEnv tyEnv tys)
>   qual tcEnv tyEnv (ListType ty) = ListType (qual tcEnv tyEnv ty)
>   qual tcEnv tyEnv (ArrowType ty1 ty2) =
>     ArrowType (qual tcEnv tyEnv ty1) (qual tcEnv tyEnv ty2)

> instance Qual (MethodSig a) where
>   qual tcEnv tyEnv (MethodSig p fs ty) = MethodSig p fs (qual tcEnv tyEnv ty)
>   qual tcEnv tyEnv (DefaultMethodDecl p f eqs) =
>     DefaultMethodDecl p f (qual tcEnv tyEnv eqs)

> instance Qual (MethodDecl a) where
>   qual tcEnv tyEnv (MethodDecl p f eqs) =
>     MethodDecl p f (qual tcEnv tyEnv eqs)

> instance Qual (Decl a) where
>   qual _ _ (InfixDecl p fix pr ops) = InfixDecl p fix pr ops
>   qual tcEnv tyEnv (TypeSig p fs ty) = TypeSig p fs (qual tcEnv tyEnv ty)
>   qual tcEnv tyEnv (FunctionDecl p f eqs) =
>     FunctionDecl p f (qual tcEnv tyEnv eqs)
>   qual tcEnv tyEnv (ForeignDecl p cc ie f ty) =
>     ForeignDecl p cc ie f (qual tcEnv tyEnv ty)
>   qual tcEnv tyEnv (PatternDecl p t rhs) =
>     PatternDecl p (qual tcEnv tyEnv t) (qual tcEnv tyEnv rhs)
>   qual _ _ (FreeDecl p vs) = (FreeDecl p vs)
>   qual _ _ (TrustAnnot p tr fs) = (TrustAnnot p tr fs)

> instance Qual (Equation a) where
>   qual tcEnv tyEnv (Equation p lhs rhs) =
>     Equation p (qual tcEnv tyEnv lhs) (qual tcEnv tyEnv rhs)

> instance Qual (Lhs a) where
>   qual tcEnv tyEnv (FunLhs f ts) = FunLhs f (qual tcEnv tyEnv ts)
>   qual tcEnv tyEnv (OpLhs t1 op t2) =
>     OpLhs (qual tcEnv tyEnv t1) op (qual tcEnv tyEnv t2)
>   qual tcEnv tyEnv (ApLhs lhs ts) =
>     ApLhs (qual tcEnv tyEnv lhs) (qual tcEnv tyEnv ts)

> instance Qual (ConstrTerm a) where
>   qual _ _ (LiteralPattern a l) = LiteralPattern a l
>   qual _ _ (NegativePattern a l) = NegativePattern a l
>   qual _ _ (VariablePattern a v) = VariablePattern a v
>   qual tcEnv tyEnv (ConstructorPattern a c ts) =
>     ConstructorPattern a (qualIdent tyEnv c) (qual tcEnv tyEnv ts)
>   qual tcEnv tyEnv (InfixPattern a t1 op t2) =
>     InfixPattern a (qual tcEnv tyEnv t1)
>                  (qualIdent tyEnv op)
>                  (qual tcEnv tyEnv t2)
>   qual tcEnv tyEnv (ParenPattern t) = ParenPattern (qual tcEnv tyEnv t)
>   qual tcEnv tyEnv (TuplePattern ts) = TuplePattern (qual tcEnv tyEnv ts)
>   qual tcEnv tyEnv (ListPattern a ts) = ListPattern a (qual tcEnv tyEnv ts)
>   qual tcEnv tyEnv (AsPattern v t) = AsPattern v (qual tcEnv tyEnv t)
>   qual tcEnv tyEnv (LazyPattern t) = LazyPattern (qual tcEnv tyEnv t)

> instance Qual (Rhs a) where
>   qual tcEnv tyEnv (SimpleRhs p e ds) =
>     SimpleRhs p (qual tcEnv tyEnv e) (qual tcEnv tyEnv ds) 
>   qual tcEnv tyEnv (GuardedRhs es ds) =
>     GuardedRhs (qual tcEnv tyEnv es) (qual tcEnv tyEnv ds)

> instance Qual (CondExpr a) where
>   qual tcEnv tyEnv (CondExpr p g e) =
>     CondExpr p (qual tcEnv tyEnv g) (qual tcEnv tyEnv e)

> instance Qual (Expression a) where
>   qual _ _ (Literal a l) = Literal a l
>   qual tcEnv tyEnv (Variable a v) = Variable a (qualIdent tyEnv v)
>   qual tcEnv tyEnv (Constructor a c) = Constructor a (qualIdent tyEnv c)
>   qual tcEnv tyEnv (Paren e) = Paren (qual tcEnv tyEnv e)
>   qual tcEnv tyEnv (Typed e ty) = Typed (qual tcEnv tyEnv e) ty
>   qual tcEnv tyEnv (Tuple es) = Tuple (qual tcEnv tyEnv es)
>   qual tcEnv tyEnv (List a es) = List a (qual tcEnv tyEnv es)
>   qual tcEnv tyEnv (ListCompr e qs) =
>     ListCompr (qual tcEnv tyEnv e) (qual tcEnv tyEnv qs)
>   qual tcEnv tyEnv (EnumFrom e) = EnumFrom (qual tcEnv tyEnv e)
>   qual tcEnv tyEnv (EnumFromThen e1 e2) =
>     EnumFromThen (qual tcEnv tyEnv e1) (qual tcEnv tyEnv e2)
>   qual tcEnv tyEnv (EnumFromTo e1 e2) =
>     EnumFromTo (qual tcEnv tyEnv e1) (qual tcEnv tyEnv e2)
>   qual tcEnv tyEnv (EnumFromThenTo e1 e2 e3) =
>     EnumFromThenTo (qual tcEnv tyEnv e1)
>                    (qual tcEnv tyEnv e2)
>                    (qual tcEnv tyEnv e3)
>   qual tcEnv tyEnv (UnaryMinus e) = UnaryMinus (qual tcEnv tyEnv e)
>   qual tcEnv tyEnv (Apply e1 e2) =
>     Apply (qual tcEnv tyEnv e1) (qual tcEnv tyEnv e2)
>   qual tcEnv tyEnv (InfixApply e1 op e2) =
>     InfixApply (qual tcEnv tyEnv e1)
>                (qual tcEnv tyEnv op)
>                (qual tcEnv tyEnv e2)
>   qual tcEnv tyEnv (LeftSection e op) =
>     LeftSection (qual tcEnv tyEnv e) (qual tcEnv tyEnv op)
>   qual tcEnv tyEnv (RightSection op e) =
>     RightSection (qual tcEnv tyEnv op) (qual tcEnv tyEnv e)
>   qual tcEnv tyEnv (Lambda ts e) =
>     Lambda (qual tcEnv tyEnv ts) (qual tcEnv tyEnv e)
>   qual tcEnv tyEnv (Let ds e) = Let (qual tcEnv tyEnv ds) (qual tcEnv tyEnv e)
>   qual tcEnv tyEnv (Do sts e) = Do (qual tcEnv tyEnv sts) (qual tcEnv tyEnv e)
>   qual tcEnv tyEnv (IfThenElse e1 e2 e3) =
>     IfThenElse (qual tcEnv tyEnv e1)
>                (qual tcEnv tyEnv e2)
>                (qual tcEnv tyEnv e3)
>   qual tcEnv tyEnv (Case e alts) =
>     Case (qual tcEnv tyEnv e) (qual tcEnv tyEnv alts)

> instance Qual (Statement a) where
>   qual tcEnv tyEnv (StmtExpr e) = StmtExpr (qual tcEnv tyEnv e)
>   qual tcEnv tyEnv (StmtBind t e) =
>     StmtBind (qual tcEnv tyEnv t) (qual tcEnv tyEnv e)
>   qual tcEnv tyEnv (StmtDecl ds) = StmtDecl (qual tcEnv tyEnv ds)

> instance Qual (Alt a) where
>   qual tcEnv tyEnv (Alt p t rhs) =
>     Alt p (qual tcEnv tyEnv t) (qual tcEnv tyEnv rhs)

> instance Qual (InfixOp a) where
>   qual tcEnv tyEnv (InfixOp a op) = InfixOp a (qualIdent tyEnv op)
>   qual tcEnv tyEnv (InfixConstr a op) = InfixConstr a (qualIdent tyEnv op)

> qualIdent :: Entity a => TopEnv a -> QualIdent -> QualIdent
> qualIdent env x
>   | isRenamed (unqualify x) = x
>   | otherwise =
>       case qualLookupTopEnv x env of
>         [y] -> origName y
>         _ -> internalError ("qualIdent: " ++ show x)

\end{verbatim}
