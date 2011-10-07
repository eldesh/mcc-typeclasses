% -*- LaTeX -*-
% $Id: CurryUtils.lhs 3057 2011-10-07 16:37:43Z wlux $
%
% Copyright (c) 1999-2011, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CurryUtils.lhs}
\section{Utilities for the Syntax Tree}
The module \texttt{CurryUtils} provides definitions that are useful
for analyzing and constructing abstract syntax trees of Curry modules
and goals.
\begin{verbatim}

> module CurryUtils where
> import Curry
> import PredefIdent

\end{verbatim}
Here is a list of predicates identifying various kinds of
declarations. Note that type class declarations are considered type
declarations because type constructors and type classes share a common
name space.
\begin{verbatim}

> isTypeDecl, isClassDecl, isInstanceDecl :: TopDecl a -> Bool
> isDefaultDecl, isBlockDecl :: TopDecl a -> Bool
> isTypeDecl (DataDecl _ _ _ _ _ _) = True
> isTypeDecl (NewtypeDecl _ _ _ _ _ _) = True
> isTypeDecl (TypeDecl _ _ _ _) = True
> isTypeDecl (ClassDecl _ _ _ _ _) = True {-sic!-}
> isTypeDecl (InstanceDecl _ _ _ _ _) = False
> isTypeDecl (DefaultDecl _ _) = False
> isTypeDecl (BlockDecl _) = False
> isClassDecl (ClassDecl _ _ _ _ _) = True
> isClassDecl _ = False
> isInstanceDecl (InstanceDecl _ _ _ _ _) = True
> isInstanceDecl _ = False
> isDefaultDecl (DefaultDecl _ _) = True
> isDefaultDecl _ = False
> isBlockDecl (BlockDecl _) = True
> isBlockDecl _ = False

> isInfixDecl, isTypeSig, isFunDecl, isFreeDecl :: Decl a -> Bool
> isTrustAnnot, isValueDecl :: Decl a -> Bool
> isInfixDecl (InfixDecl _ _ _ _) = True
> isInfixDecl _ = False
> isTypeSig (TypeSig _ _ _) = True
> isTypeSig (ForeignDecl _ _ _ _ _) = True
> isTypeSig _ = False
> isFunDecl (FunctionDecl _ _ _ _) = True
> isFunDecl (ForeignDecl _ _ _ _ _) = True
> isFunDecl _ = False
> isFreeDecl (FreeDecl _ _) = True
> isFreeDecl _ = False
> isTrustAnnot (TrustAnnot _ _ _) = True
> isTrustAnnot _ = False
> isValueDecl (FunctionDecl _ _ _ _) = True
> isValueDecl (ForeignDecl _ _ _ _ _) = True
> isValueDecl (PatternDecl _ _ _) = True
> isValueDecl (FreeDecl _ _) = True
> isValueDecl _ = False

\end{verbatim}
The function \texttt{typeConstr} returns the type constructor at the
root of a type application.
\begin{verbatim}

> typeConstr :: TypeExpr -> QualIdent
> typeConstr (ConstructorType tc) = tc
> typeConstr (TupleType tys) = qTupleId (length tys)
> typeConstr (ListType _) = qListId
> typeConstr (ArrowType _ _) = qArrowId
> typeConstr (ApplyType ty _) = typeConstr ty

\end{verbatim}
The function \texttt{isVariableType} checks whether its type
expression argument is just a type variable and the function
\texttt{isSimpleType} checks whether its type expression argument has
the form $T\,u_1 \dots u_n$ where $T$ is a type constructor and
$u_1,\dots,u_n$ are -- not necessarily distinct -- type variables.
\begin{verbatim}

> isVariableType :: TypeExpr -> Bool
> isVariableType (ConstructorType _) = False
> isVariableType (VariableType _) = True
> isVariableType (TupleType _) = False
> isVariableType (ListType _) = False
> isVariableType (ArrowType _ _) = False
> isVariableType (ApplyType _ _) = False

> isSimpleType :: TypeExpr -> Bool
> isSimpleType (ConstructorType _) = True
> isSimpleType (VariableType _) = False
> isSimpleType (TupleType tys) = all isVariableType tys
> isSimpleType (ListType ty) = isVariableType ty
> isSimpleType (ArrowType ty1 ty2) = isVariableType ty1 && isVariableType ty2
> isSimpleType (ApplyType ty1 ty2) = isSimpleType ty1 && isVariableType ty2

\end{verbatim}
The function \texttt{isVarPattern} returns true if its argument is
semantically equivalent to a variable pattern. Note that in particular
this function returns \texttt{True} for lazy patterns.
\begin{verbatim}

> isVarPattern :: ConstrTerm a -> Bool
> isVarPattern (LiteralPattern _ _) = False
> isVarPattern (NegativePattern _ _) = False
> isVarPattern (VariablePattern _ _) = True
> isVarPattern (ConstructorPattern _ _ _) = False
> isVarPattern (FunctionPattern _ _ _) = False
> isVarPattern (InfixPattern _ _ _ _) = False
> isVarPattern (ParenPattern t) = isVarPattern t
> isVarPattern (TuplePattern _) = False
> isVarPattern (ListPattern _ _) = False
> isVarPattern (AsPattern _ t) = isVarPattern t
> isVarPattern (LazyPattern _) = True

\end{verbatim}
The functions \texttt{constr} and \texttt{nconstr} return the
constructor name of a data constructor and newtype constructor
declaration, respectively.
\begin{verbatim}

> constr :: ConstrDecl -> Ident
> constr (ConstrDecl _ _ _ c _) = c
> constr (ConOpDecl _ _ _ _ op _) = op
> constr (RecordDecl _ _ _ c _) = c

> nconstr :: NewConstrDecl -> Ident
> nconstr (NewConstrDecl _ c _) = c
> nconstr (NewRecordDecl _ c _ _) = c

\end{verbatim}
The functions \texttt{labels} and \texttt{nlabel} return the field
label identifiers of a data constructor and newtype constructor
declaration, respectively.
\begin{verbatim}

> labels :: ConstrDecl -> [Ident]
> labels (ConstrDecl _ _ _ _ _) = []
> labels (ConOpDecl _ _ _ _ _ _) = []
> labels (RecordDecl _ _ _ _ fs) = [l | FieldDecl _ ls _ <- fs, l <- ls]

> nlabel :: NewConstrDecl -> [Ident]
> nlabel (NewConstrDecl _ _ _) = []
> nlabel (NewRecordDecl _ _ l _) = [l]

\end{verbatim}
The functions \texttt{methods} and \texttt{imethod} return the
declared method identifiers of a type class method declaration in
source and interface modules, respectively.
\begin{verbatim}

> methods :: Decl a -> [Ident]
> methods (InfixDecl _ _ _ _) = []
> methods (TypeSig _ fs _) = fs
> methods (FunctionDecl _ _ _ _) = []
> methods (TrustAnnot _ _ _) = []

> imethod :: IMethodDecl -> Ident
> imethod (IMethodDecl _ f _ _) = f

\end{verbatim}
The function \texttt{eqnArity} returns the (syntactic) arity of a
function equation and \texttt{flatLhs} returns the function name and
the list of arguments from the left hand side of a function equation.
\begin{verbatim}

> eqnArity :: Equation a -> Int
> eqnArity (Equation _ lhs _) = length (snd (flatLhs lhs))

> flatLhs :: Lhs a -> (Ident,[ConstrTerm a])
> flatLhs lhs = flat lhs []
>   where flat (FunLhs f ts) ts' = (f,ts ++ ts')
>         flat (OpLhs t1 op t2) ts = (op,t1:t2:ts)
>         flat (ApLhs lhs ts) ts' = flat lhs (ts ++ ts')

\end{verbatim}
The function \texttt{infixOp} converts an infix operator into an
expression and the function \texttt{opName} returns the operator's
name.
\begin{verbatim}

> infixOp :: InfixOp a -> Expression a
> infixOp (InfixOp a op) = Variable a op
> infixOp (InfixConstr a op) = Constructor a op

> opName :: InfixOp a -> QualIdent
> opName (InfixOp _ op) = op
> opName (InfixConstr _ c) = c

\end{verbatim}
The function \texttt{orderFields} sorts the arguments of a record
pattern or expression into a fixed order, which usually is the order
in which the labels appear in the record's declaration.
\begin{verbatim}

> orderFields :: [Field a] -> [Ident] -> [Maybe a]
> orderFields fs ls = map (flip lookup [(unqualify l,x) | Field l x <- fs]) ls

\end{verbatim}
The function \texttt{entity} returns the qualified name of the entity
defined by an interface declaration.
\begin{verbatim}

> entity :: IDecl -> QualIdent
> entity (IInfixDecl _ _ _ op) = op
> entity (HidingDataDecl _ tc _ _) = tc
> entity (IDataDecl _ _ tc _ _ _ _) = tc
> entity (INewtypeDecl _ _ tc _ _ _ _) = tc
> entity (ITypeDecl _ tc _ _ _) = tc
> entity (HidingClassDecl _ _ cls _ _) = cls
> entity (IClassDecl _ _ cls _ _ _ _) = cls
> entity (IInstanceDecl _ _ _ _ m _) = maybe qualify qualifyWith m anonId
> entity (IFunctionDecl _ f _ _) = f

\end{verbatim}
The function \texttt{unhide} makes interface declarations transparent,
i.e., it replaces hidden data type and class declarations by standard
data type and class declarations, respectively, and removes all hiding
specifications from interface declarations.
\begin{verbatim}

> unhide :: IDecl -> IDecl
> unhide (IInfixDecl p fix pr op) = IInfixDecl p fix pr op
> unhide (HidingDataDecl p tc k tvs) = IDataDecl p [] tc k tvs [] []
> unhide (IDataDecl p cx tc k tvs cs _) = IDataDecl p cx tc k tvs cs []
> unhide (INewtypeDecl p cx tc k tvs nc _) = INewtypeDecl p cx tc k tvs nc []
> unhide (ITypeDecl p tc k tvs ty) = ITypeDecl p tc k tvs ty
> unhide (HidingClassDecl p cx cls k tv) = IClassDecl p cx cls k tv [] []
> unhide (IClassDecl p cx cls k tv ds _) = IClassDecl p cx cls k tv ds []
> unhide (IInstanceDecl p cx cls ty m fs) = IInstanceDecl p cx cls ty m fs
> unhide (IFunctionDecl p f n ty) = IFunctionDecl p f n ty

\end{verbatim}
Here are a few convenience functions for constructing (elements of)
abstract syntax trees.
\begin{verbatim}

> funDecl :: Position -> a -> Ident -> [ConstrTerm a] -> Expression a -> Decl a
> funDecl p a f ts e = FunctionDecl p a f [funEqn p f ts e]

> funEqn :: Position -> Ident -> [ConstrTerm a] -> Expression a -> Equation a
> funEqn p f ts e = Equation p (FunLhs f ts) (SimpleRhs p e [])

> patDecl :: Position -> ConstrTerm a -> Expression a -> Decl a
> patDecl p t e = PatternDecl p t (SimpleRhs p e [])

> varDecl :: Position -> a -> Ident -> Expression a -> Decl a
> varDecl p ty = patDecl p . VariablePattern ty

> caseAlt :: Position -> ConstrTerm a -> Expression a -> Alt a
> caseAlt p t e = Alt p t (SimpleRhs p e [])

> mkLet :: [Decl a] -> Expression a -> Expression a
> mkLet ds e = if null ds then e else Let ds e

> apply :: Expression a -> [Expression a] -> Expression a
> apply = foldl Apply

> mkVar :: a -> Ident -> Expression a
> mkVar ty = Variable ty . qualify

\end{verbatim}
