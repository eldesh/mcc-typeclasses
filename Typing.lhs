% -*- LaTeX -*-
% $Id: Typing.lhs 1999 2006-11-10 21:53:29Z wlux $
%
% Copyright (c) 2003-2006, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Typing.lhs}
\section{Computing the Type of Curry Expressions}
\begin{verbatim}

> module Typing(Typeable(..)) where
> import Base

\end{verbatim}
After the compiler has attributed patterns and expressions with type
information during type inference, it is straight forward to recompute
the type of every pattern and expression. Since all annotated types
are monomorphic, there is no need to instantiate any variables or
perform any (non-trivial) unifications.
\begin{verbatim}

> class Typeable a where
>   typeOf :: a -> Type

> instance Typeable Type where
>   typeOf = id

> instance Typeable Literal where
>   typeOf = litType

> instance Typeable a => Typeable (ConstrTerm a) where
>   typeOf = argType

> instance Typeable a => Typeable (Expression a) where
>   typeOf = exprType

> instance Typeable a => Typeable (Rhs a) where
>   typeOf = rhsType

> litType :: Literal -> Type
> litType (Char _) = charType
> litType (Int _) = intType
> litType (Float _) = floatType
> litType (String _) = stringType

> argType :: Typeable a => ConstrTerm a -> Type
> argType (LiteralPattern a _) = typeOf a
> argType (NegativePattern a _) = typeOf a
> argType (VariablePattern a _) = typeOf a
> argType (ConstructorPattern a _ _) = typeOf a
> argType (InfixPattern a _ _ _) = typeOf a
> argType (ParenPattern t) = argType t
> argType (TuplePattern ts) = tupleType (map argType ts)
> argType (ListPattern a _) = typeOf a
> argType (AsPattern _ t) = argType t
> argType (LazyPattern t) = argType t

> exprType :: Typeable a => Expression a -> Type
> exprType (Literal a _) = typeOf a
> exprType (Variable a _) = typeOf a
> exprType (Constructor a _) = typeOf a
> exprType (Typed e _) = exprType e
> exprType (Paren e) = exprType e
> exprType (Tuple es) = tupleType (map exprType es)
> exprType (List a _) = typeOf a
> exprType (ListCompr e _) = listType (exprType e)
> exprType (EnumFrom e) = listType (exprType e)
> exprType (EnumFromThen e _) = listType (exprType e)
> exprType (EnumFromTo e _) = listType (exprType e)
> exprType (EnumFromThenTo e _ _) = listType (exprType e)
> exprType (UnaryMinus e) = exprType e
> exprType (Apply f e) =
>   case exprType f of
>     TypeArrow ty1 ty2 | ty1 == exprType e -> ty2
>     _ -> internalError "exprType (Apply)"
> exprType (InfixApply e1 op e2) =
>   case exprType (infixOp op) of
>     TypeArrow ty1 (TypeArrow ty2 ty3)
>       | ty1 == exprType e1 && ty2 == exprType e2 -> ty3
>     _ -> internalError "exprType (InfixApply)"
> exprType (LeftSection e op) =
>   case exprType (infixOp op) of
>     TypeArrow ty1 ty2 | ty1 == exprType e -> ty2
>     _ -> internalError "exprType (LeftSection)"
> exprType (RightSection op e) =
>   case exprType (infixOp op) of
>     TypeArrow ty1 (TypeArrow ty2 ty3) | ty2 == exprType e -> TypeArrow ty1 ty3
>     _ -> internalError "exprType (RightSection)"
> exprType (Lambda ts e) = foldr TypeArrow (exprType e) (map argType ts)
> exprType (Let _ e) = exprType e
> exprType (Do _ e) = exprType e
> exprType (IfThenElse _ e _) = exprType e
> exprType (Case _ as) = head [rhsType rhs | Alt _ _ rhs <- as]

> rhsType :: Typeable a => Rhs a -> Type
> rhsType (SimpleRhs _ e _) = exprType e
> rhsType (GuardedRhs es _) = head [exprType e | CondExpr _ _ e <- es]

\end{verbatim}
