% -*- LaTeX -*-
% $Id: CurrySyntax.lhs 1973 2006-09-19 19:06:48Z wlux $
%
% Copyright (c) 1999-2006, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CurrySyntax.lhs}
\section{The Parse Tree}
This module provides the necessary data structures to maintain the
parsed representation of a Curry program.
\begin{verbatim}

> module CurrySyntax where
> import Ident
> import Position

\end{verbatim}
\paragraph{Modules}
\begin{verbatim}

> data Module =
>   Module ModuleIdent (Maybe ExportSpec) [ImportDecl] [TopDecl]
>   deriving (Eq,Show)

> data ExportSpec = Exporting Position [Export] deriving (Eq,Show)
> data Export =
>     Export         QualIdent                  -- f/T
>   | ExportTypeWith QualIdent [Ident]          -- T(C1,...,Cn)
>   | ExportTypeAll  QualIdent                  -- T(..)
>   | ExportModule   ModuleIdent
>   deriving (Eq,Show)

> data ImportDecl =
>   ImportDecl Position ModuleIdent Qualified (Maybe ModuleIdent)
>              (Maybe ImportSpec)
>   deriving (Eq,Show)
> data ImportSpec =
>     Importing Position [Import]
>   | Hiding Position [Import]
>   deriving (Eq,Show)
> data Import =
>     Import         Ident            -- f/T
>   | ImportTypeWith Ident [Ident]    -- T(C1,...,Cn)
>   | ImportTypeAll  Ident            -- T(..)
>   deriving (Eq,Show)

> type Qualified = Bool

\end{verbatim}
\paragraph{Module declarations}
\begin{verbatim}

> data TopDecl =
>     DataDecl Position Ident [Ident] [ConstrDecl]
>   | NewtypeDecl Position Ident [Ident] NewConstrDecl
>   | TypeDecl Position Ident [Ident] TypeExpr
>   | ClassDecl Position Ident Ident
>   | BlockDecl Decl
>   deriving (Eq,Show)

> data ConstrDecl =
>     ConstrDecl Position [Ident] Ident [TypeExpr]
>   | ConOpDecl Position [Ident] TypeExpr Ident TypeExpr
>   deriving (Eq,Show)
> data NewConstrDecl = NewConstrDecl Position Ident TypeExpr deriving (Eq,Show)

> data Decl =
>     InfixDecl Position Infix Int [Ident]
>   | TypeSig Position [Ident] TypeExpr
>   | FunctionDecl Position Ident [Equation]
>   | ForeignDecl Position CallConv (Maybe String) Ident TypeExpr
>   | PatternDecl Position ConstrTerm Rhs
>   | FreeDecl Position [Ident]
>   | TrustAnnot Position Trust (Maybe [Ident])
>   deriving (Eq,Show)

> data Infix = Infix | InfixL | InfixR deriving (Eq,Show)
> data CallConv = CallConvPrimitive | CallConvCCall deriving (Eq,Show)
> data Trust = Suspect | Trust deriving (Eq,Show)

> constr :: ConstrDecl -> Ident
> constr (ConstrDecl _ _ c _) = c
> constr (ConOpDecl _ _ _ op _) = op

> nconstr :: NewConstrDecl -> Ident
> nconstr (NewConstrDecl _ c _) = c

\end{verbatim}
\paragraph{Module interfaces}
Interface declarations are restricted to type declarations and signatures.
\begin{verbatim}

> data Interface =
>   Interface ModuleIdent [IImportDecl] [IDecl]
>   deriving (Eq,Show)

> data IImportDecl = IImportDecl Position ModuleIdent deriving (Eq,Show)

> data IDecl =
>     IInfixDecl Position Infix Int QualIdent
>   | HidingDataDecl Position QualIdent [Ident] 
>   | IDataDecl Position QualIdent [Ident] [Maybe ConstrDecl]
>   | INewtypeDecl Position QualIdent [Ident] NewConstrDecl
>   | ITypeDecl Position QualIdent [Ident] TypeExpr
>   | IClassDecl Position QualIdent Ident
>   | IFunctionDecl Position QualIdent TypeExpr
>   deriving (Eq,Show)

\end{verbatim}
\paragraph{Types}
\begin{verbatim}

> data TypeExpr =
>     ConstructorType QualIdent [TypeExpr]
>   | VariableType Ident
>   | TupleType [TypeExpr]
>   | ListType TypeExpr
>   | ArrowType TypeExpr TypeExpr
>   deriving (Eq,Show)

\end{verbatim}
\paragraph{Functions}
\begin{verbatim}

> data Equation = Equation Position Lhs Rhs deriving (Eq,Show)
> data Lhs =
>     FunLhs Ident [ConstrTerm]
>   | OpLhs ConstrTerm Ident ConstrTerm
>   | ApLhs Lhs [ConstrTerm]
>   deriving (Eq,Show)
> data Rhs =
>     SimpleRhs Position Expression [Decl]
>   | GuardedRhs [CondExpr] [Decl]
>   deriving (Eq,Show)
> data CondExpr = CondExpr Position Expression Expression deriving (Eq,Show)

> flatLhs :: Lhs -> (Ident,[ConstrTerm])
> flatLhs lhs = flat lhs []
>   where flat (FunLhs f ts) ts' = (f,ts ++ ts')
>         flat (OpLhs t1 op t2) ts = (op,t1:t2:ts)
>         flat (ApLhs lhs ts) ts' = flat lhs (ts ++ ts')

\end{verbatim}
\paragraph{Literals} The \texttt{Ident} argument of an \texttt{Int}
literal is used for supporting ad-hoc polymorphism on integer
numbers. An integer literal can be used either as an integer number or
as a floating-point number depending on its context. The compiler uses
the identifier of the \texttt{Int} literal for maintaining its type.
\begin{verbatim}

> data Literal =
>     Char Char                         -- should be Int to handle Unicode
>   | Int Ident Int
>   | Float Double
>   | String String                     -- should be [Int] to handle Unicode
>   deriving (Eq,Show)

\end{verbatim}
\paragraph{Patterns}
\begin{verbatim}

> data ConstrTerm =
>     LiteralPattern Literal
>   | NegativePattern Ident Literal
>   | VariablePattern Ident
>   | ConstructorPattern QualIdent [ConstrTerm]
>   | InfixPattern ConstrTerm QualIdent ConstrTerm
>   | ParenPattern ConstrTerm
>   | TuplePattern [ConstrTerm]
>   | ListPattern [ConstrTerm]
>   | AsPattern Ident ConstrTerm
>   | LazyPattern ConstrTerm
>   deriving (Eq,Show)

\end{verbatim}
\paragraph{Expressions}
\begin{verbatim}

> data Expression =
>     Literal Literal
>   | Variable QualIdent
>   | Constructor QualIdent
>   | Paren Expression
>   | Typed Expression TypeExpr
>   | Tuple [Expression]
>   | List [Expression]
>   | ListCompr Expression [Statement]
>   | EnumFrom Expression
>   | EnumFromThen Expression Expression
>   | EnumFromTo Expression Expression
>   | EnumFromThenTo Expression Expression Expression
>   | UnaryMinus Ident Expression
>   | Apply Expression Expression
>   | InfixApply Expression InfixOp Expression
>   | LeftSection Expression InfixOp
>   | RightSection InfixOp Expression
>   | Lambda [ConstrTerm] Expression
>   | Let [Decl] Expression
>   | Do [Statement] Expression
>   | IfThenElse Expression Expression Expression
>   | Case Expression [Alt]
>   deriving (Eq,Show)

> data InfixOp = InfixOp QualIdent | InfixConstr QualIdent deriving (Eq,Show)

> data Statement =
>     StmtExpr Expression
>   | StmtDecl [Decl]
>   | StmtBind ConstrTerm Expression
>   deriving (Eq,Show)

> data Alt = Alt Position ConstrTerm Rhs deriving (Eq,Show)

> opName :: InfixOp -> QualIdent
> opName (InfixOp op) = op
> opName (InfixConstr c) = c

\end{verbatim}
\paragraph{Goals}
A goal is equivalent to an unconditional right hand side of an equation.
\begin{verbatim}

> data Goal = Goal Position Expression [Decl] deriving (Eq,Show)

\end{verbatim}
