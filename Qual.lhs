% -*- LaTeX -*-
% $Id: Qual.lhs 2684 2008-04-23 17:46:29Z wlux $
%
% Copyright (c) 2001-2008, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Qual.lhs}
\section{Qualification}
After syntax checking and before kind checking, the compiler removes
unnecessary module qualifiers from all identifiers in the current
module and changes the module qualifiers of those entities whose name
would otherwise be ambiguous to match the modules containing their
definitions. This policy allows the compiler to add references to
prelude entities into the source code without risk of name conflicts
and at the same time avoids messing up error messages with lots of
redundant module qualifiers.

After type checking succeeds, the compiler adds correct module
qualifiers to all entites except for entities defined in local
declaration groups.

Exporting the types \texttt{Qual} and \texttt{Phase} is necessary in
order to compile this module with hbc.
\begin{verbatim}

> module Qual(Qual, Phase, qual1, qual2) where
> import Base
> import Curry
> import IdentInfo
> import TopEnv

> data Phase = One | Two

> qual1, qual2 :: Qual a => TypeEnv -> FunEnv -> a -> a
> qual1 = qual One
> qual2 = qual Two

> class Qual a where
>   qual :: Phase -> TypeEnv -> FunEnv -> a -> a

> instance Qual a => Qual [a] where
>   qual phase tEnv vEnv = map (qual phase tEnv vEnv)

> instance Qual (Goal a) where
>   qual phase tEnv vEnv (Goal p e ds) =
>     Goal p (qual phase tEnv vEnv e) (qual phase tEnv vEnv ds)

> instance Qual (TopDecl a) where
>   qual phase tEnv vEnv (DataDecl p cx tc tvs cs clss) =
>     DataDecl p (qual phase tEnv vEnv cx) tc tvs (qual phase tEnv vEnv cs)
>              (map (qualIdent phase tEnv) clss)
>   qual phase tEnv vEnv (NewtypeDecl p cx tc tvs nc clss) =
>     NewtypeDecl p (qual phase tEnv vEnv cx) tc tvs
>                 (qual phase tEnv vEnv nc)
>                 (map (qualIdent phase tEnv) clss)
>   qual phase tEnv vEnv (TypeDecl p tc tvs ty) =
>     TypeDecl p tc tvs (qual phase tEnv vEnv ty)
>   qual phase tEnv vEnv (ClassDecl p cx cls tv ds) =
>     ClassDecl p (qual phase tEnv vEnv cx) cls tv (qual phase tEnv vEnv ds)
>   qual phase tEnv vEnv (InstanceDecl p cx cls ty ds) =
>     InstanceDecl p (qual phase tEnv vEnv cx)
>                  (qualIdent phase tEnv cls)
>                  (qual phase tEnv vEnv ty)
>                  (qual phase tEnv vEnv ds)
>   qual phase tEnv vEnv (DefaultDecl p tys) =
>     DefaultDecl p (qual phase tEnv vEnv tys)
>   qual phase tEnv vEnv (BlockDecl d) = BlockDecl (qual phase tEnv vEnv d)

> instance Qual ConstrDecl where
>   qual phase tEnv vEnv (ConstrDecl p evs cx c tys) =
>     ConstrDecl p evs (qual phase tEnv vEnv cx) c (qual phase tEnv vEnv tys)
>   qual phase tEnv vEnv (ConOpDecl p evs cx ty1 op ty2) =
>     ConOpDecl p evs (qual phase tEnv vEnv cx)
>               (qual phase tEnv vEnv ty1) op (qual phase tEnv vEnv ty2)
>   qual phase tEnv vEnv (RecordDecl p evs cx c fs) =
>     RecordDecl p evs (qual phase tEnv vEnv cx) c (qual phase tEnv vEnv fs)

> instance Qual FieldDecl where
>   qual phase tEnv vEnv (FieldDecl p ls ty) =
>     FieldDecl p ls (qual phase tEnv vEnv ty)

> instance Qual NewConstrDecl where
>   qual phase tEnv vEnv (NewConstrDecl p c ty) =
>     NewConstrDecl p c (qual phase tEnv vEnv ty)
>   qual phase tEnv vEnv (NewRecordDecl p c l ty) =
>     NewRecordDecl p c l (qual phase tEnv vEnv ty)

> instance Qual QualTypeExpr where
>   qual phase tEnv vEnv (QualTypeExpr cx ty) =
>     QualTypeExpr (qual phase tEnv vEnv cx) (qual phase tEnv vEnv ty)

> instance Qual ClassAssert where
>   qual phase tEnv vEnv (ClassAssert cls ty) =
>     ClassAssert (qualIdent phase tEnv cls) (qual phase tEnv vEnv ty)

> instance Qual TypeExpr where
>   qual phase tEnv vEnv (ConstructorType c) =
>     ConstructorType (qualIdent phase tEnv c)
>   qual _ _ _ (VariableType tv) = VariableType tv
>   qual phase tEnv vEnv (TupleType tys) = TupleType (qual phase tEnv vEnv tys)
>   qual phase tEnv vEnv (ListType ty) = ListType (qual phase tEnv vEnv ty)
>   qual phase tEnv vEnv (ArrowType ty1 ty2) =
>     ArrowType (qual phase tEnv vEnv ty1) (qual phase tEnv vEnv ty2)
>   qual phase tEnv vEnv (ApplyType ty1 ty2) =
>     ApplyType (qual phase tEnv vEnv ty1) (qual phase tEnv vEnv ty2)

> instance Qual (Decl a) where
>   qual _ _ _ (InfixDecl p fix pr ops) = InfixDecl p fix pr ops
>   qual phase tEnv vEnv (TypeSig p fs ty) =
>     TypeSig p fs (qual phase tEnv vEnv ty)
>   qual phase tEnv vEnv (FunctionDecl p f eqs) =
>     FunctionDecl p f (qual phase tEnv vEnv eqs)
>   qual phase tEnv vEnv (ForeignDecl p cc s ie f ty) =
>     ForeignDecl p cc s ie f (qual phase tEnv vEnv ty)
>   qual phase tEnv vEnv (PatternDecl p t rhs) =
>     PatternDecl p (qual phase tEnv vEnv t) (qual phase tEnv vEnv rhs)
>   qual _ _ _ (FreeDecl p vs) = FreeDecl p vs
>   qual _ _ _ (TrustAnnot p tr fs) = TrustAnnot p tr fs

> instance Qual (Equation a) where
>   qual phase tEnv vEnv (Equation p lhs rhs) =
>     Equation p (qual phase tEnv vEnv lhs) (qual phase tEnv vEnv rhs)

> instance Qual (Lhs a) where
>   qual phase tEnv vEnv (FunLhs f ts) = FunLhs f (qual phase tEnv vEnv ts)
>   qual phase tEnv vEnv (OpLhs t1 op t2) =
>     OpLhs (qual phase tEnv vEnv t1) op (qual phase tEnv vEnv t2)
>   qual phase tEnv vEnv (ApLhs lhs ts) =
>     ApLhs (qual phase tEnv vEnv lhs) (qual phase tEnv vEnv ts)

> instance Qual (ConstrTerm a) where
>   qual _ _ _ (LiteralPattern a l) = LiteralPattern a l
>   qual _ _ _ (NegativePattern a l) = NegativePattern a l
>   qual _ _ _ (VariablePattern a v) = VariablePattern a v
>   qual phase tEnv vEnv (ConstructorPattern a c ts) =
>     ConstructorPattern a (qualIdent phase vEnv c) (qual phase tEnv vEnv ts)
>   qual phase tEnv vEnv (InfixPattern a t1 op t2) =
>     InfixPattern a (qual phase tEnv vEnv t1)
>                  (qualIdent phase vEnv op)
>                  (qual phase tEnv vEnv t2)
>   qual phase tEnv vEnv (ParenPattern t) =
>     ParenPattern (qual phase tEnv vEnv t)
>   qual phase tEnv vEnv (RecordPattern a c fs) =
>     RecordPattern a (qualIdent phase vEnv c) (qual phase tEnv vEnv fs)
>   qual phase tEnv vEnv (TuplePattern ts) =
>     TuplePattern (qual phase tEnv vEnv ts)
>   qual phase tEnv vEnv (ListPattern a ts) =
>     ListPattern a (qual phase tEnv vEnv ts)
>   qual phase tEnv vEnv (AsPattern v t) = AsPattern v (qual phase tEnv vEnv t)
>   qual phase tEnv vEnv (LazyPattern t) = LazyPattern (qual phase tEnv vEnv t)

> instance Qual (Rhs a) where
>   qual phase tEnv vEnv (SimpleRhs p e ds) =
>     SimpleRhs p (qual phase tEnv vEnv e) (qual phase tEnv vEnv ds) 
>   qual phase tEnv vEnv (GuardedRhs es ds) =
>     GuardedRhs (qual phase tEnv vEnv es) (qual phase tEnv vEnv ds)

> instance Qual (CondExpr a) where
>   qual phase tEnv vEnv (CondExpr p g e) =
>     CondExpr p (qual phase tEnv vEnv g) (qual phase tEnv vEnv e)

> instance Qual (Expression a) where
>   qual _ _ _ (Literal a l) = Literal a l
>   qual phase _ vEnv (Variable a v) = Variable a (qualIdent phase vEnv v)
>   qual phase _ vEnv (Constructor a c) = Constructor a (qualIdent phase vEnv c)
>   qual phase tEnv vEnv (Paren e) = Paren (qual phase tEnv vEnv e)
>   qual phase tEnv vEnv (Typed e ty) =
>     Typed (qual phase tEnv vEnv e) (qual phase tEnv vEnv ty)
>   qual phase tEnv vEnv (Record a c fs) =
>     Record a (qualIdent phase vEnv c) (qual phase tEnv vEnv fs)
>   qual phase tEnv vEnv (RecordUpdate e fs) =
>     RecordUpdate (qual phase tEnv vEnv e) (qual phase tEnv vEnv fs)
>   qual phase tEnv vEnv (Tuple es) = Tuple (qual phase tEnv vEnv es)
>   qual phase tEnv vEnv (List a es) = List a (qual phase tEnv vEnv es)
>   qual phase tEnv vEnv (ListCompr e qs) =
>     ListCompr (qual phase tEnv vEnv e) (qual phase tEnv vEnv qs)
>   qual phase tEnv vEnv (EnumFrom e) = EnumFrom (qual phase tEnv vEnv e)
>   qual phase tEnv vEnv (EnumFromThen e1 e2) =
>     EnumFromThen (qual phase tEnv vEnv e1) (qual phase tEnv vEnv e2)
>   qual phase tEnv vEnv (EnumFromTo e1 e2) =
>     EnumFromTo (qual phase tEnv vEnv e1) (qual phase tEnv vEnv e2)
>   qual phase tEnv vEnv (EnumFromThenTo e1 e2 e3) =
>     EnumFromThenTo (qual phase tEnv vEnv e1)
>                    (qual phase tEnv vEnv e2)
>                    (qual phase tEnv vEnv e3)
>   qual phase tEnv vEnv (UnaryMinus e) = UnaryMinus (qual phase tEnv vEnv e)
>   qual phase tEnv vEnv (Apply e1 e2) =
>     Apply (qual phase tEnv vEnv e1) (qual phase tEnv vEnv e2)
>   qual phase tEnv vEnv (InfixApply e1 op e2) =
>     InfixApply (qual phase tEnv vEnv e1)
>                (qual phase tEnv vEnv op)
>                (qual phase tEnv vEnv e2)
>   qual phase tEnv vEnv (LeftSection e op) =
>     LeftSection (qual phase tEnv vEnv e) (qual phase tEnv vEnv op)
>   qual phase tEnv vEnv (RightSection op e) =
>     RightSection (qual phase tEnv vEnv op) (qual phase tEnv vEnv e)
>   qual phase tEnv vEnv (Lambda p ts e) =
>     Lambda p (qual phase tEnv vEnv ts) (qual phase tEnv vEnv e)
>   qual phase tEnv vEnv (Let ds e) =
>     Let (qual phase tEnv vEnv ds) (qual phase tEnv vEnv e)
>   qual phase tEnv vEnv (Do sts e) =
>     Do (qual phase tEnv vEnv sts) (qual phase tEnv vEnv e)
>   qual phase tEnv vEnv (IfThenElse e1 e2 e3) =
>     IfThenElse (qual phase tEnv vEnv e1)
>                (qual phase tEnv vEnv e2)
>                (qual phase tEnv vEnv e3)
>   qual phase tEnv vEnv (Case e alts) =
>     Case (qual phase tEnv vEnv e) (qual phase tEnv vEnv alts)
>   qual phase tEnv vEnv (Fcase e alts) =
>     Fcase (qual phase tEnv vEnv e) (qual phase tEnv vEnv alts)

> instance Qual (Statement a) where
>   qual phase tEnv vEnv (StmtExpr e) = StmtExpr (qual phase tEnv vEnv e)
>   qual phase tEnv vEnv (StmtBind p t e) =
>     StmtBind p (qual phase tEnv vEnv t) (qual phase tEnv vEnv e)
>   qual phase tEnv vEnv (StmtDecl ds) = StmtDecl (qual phase tEnv vEnv ds)

> instance Qual (Alt a) where
>   qual phase tEnv vEnv (Alt p t rhs) =
>     Alt p (qual phase tEnv vEnv t) (qual phase tEnv vEnv rhs)

> instance Qual (InfixOp a) where
>   qual phase _ vEnv (InfixOp a op) = InfixOp a (qualIdent phase vEnv op)
>   qual phase _ vEnv (InfixConstr a op) =
>     InfixConstr a (qualIdent phase vEnv op)

> instance Qual a => Qual (Field a) where
>   qual phase tEnv vEnv (Field l x) =
>     Field (qualIdent phase vEnv l) (qual phase tEnv vEnv x)

> qualIdent :: Entity a => Phase -> TopEnv a -> QualIdent -> QualIdent
> qualIdent One env x
>   | isQualified x =
>       case qualLookupTopEnv x env of
>         [y] ->
>           case lookupTopEnv x' env of
>             [z] | origName y == origName z -> qualify x'
>             _ -> origName y
>           where x' = unqualify x
>         _ -> internalError ("qualIdent: " ++ show x)
>   | otherwise = x
> qualIdent Two env x
>   | isQualified x || isRenamed (unqualify x) = x
>   | otherwise =
>       case qualLookupTopEnv x env of
>         [y] -> origName y
>         _ -> internalError ("qualIdent: " ++ show x)

\end{verbatim}
