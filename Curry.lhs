% -*- LaTeX -*-
% $Id: Curry.lhs 3056 2011-10-07 16:27:03Z wlux $
%
% Copyright (c) 1999-2011, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Curry.lhs}
\section{The Parse Tree}
This module provides the necessary data structures to maintain the
parsed representation of a Curry program. The syntax tree carries
attributes for literals, variables, and constructors appearing in
patterns and expressions. At present, these attributes are used for
associating types with patterns and expressions after type inference.
\begin{verbatim}

> module Curry(module Curry, module Ident, Position) where
> import Ident
> import Position

\end{verbatim}
\paragraph{Modules}
\begin{verbatim}

> data Module a =
>   Module ModuleIdent (Maybe ExportSpec) [ImportDecl] [TopDecl a]
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

> data TopDecl a =
>     DataDecl Position [ClassAssert] Ident [Ident] [ConstrDecl] [DClass]
>   | NewtypeDecl Position [ClassAssert] Ident [Ident] NewConstrDecl [DClass]
>   | TypeDecl Position Ident [Ident] TypeExpr
>   | ClassDecl Position [ClassAssert] Ident Ident [Decl a]
>   | InstanceDecl Position [ClassAssert] QualIdent TypeExpr [Decl a]
>   | DefaultDecl Position [TypeExpr]
>   | BlockDecl (Decl a)
>   deriving (Eq,Show)

> data DClass = DClass Position QualIdent deriving (Eq,Show)

> data ConstrDecl =
>     ConstrDecl Position [Ident] [ClassAssert] Ident [TypeExpr]
>   | ConOpDecl Position [Ident] [ClassAssert] TypeExpr Ident TypeExpr
>   | RecordDecl Position [Ident] [ClassAssert] Ident [FieldDecl]
>   deriving (Eq,Show)
> data NewConstrDecl =
>     NewConstrDecl Position Ident TypeExpr
>   | NewRecordDecl Position Ident Ident TypeExpr
>   deriving (Eq,Show)

> data FieldDecl = FieldDecl Position [Ident] TypeExpr deriving (Eq,Show)

> data Decl a =
>     InfixDecl Position Infix (Maybe Integer) [Ident]
>   | TypeSig Position [Ident] QualTypeExpr
>   | FunctionDecl Position a Ident [Equation a]
>   | ForeignDecl Position ForeignImport a Ident TypeExpr
>   | PatternDecl Position (ConstrTerm a) (Rhs a)
>   | FreeDecl Position [FreeVar a]
>   | TrustAnnot Position Trust [Ident]
>   deriving (Eq,Show)

> data Infix = Infix | InfixL | InfixR deriving (Eq,Show)
> type ForeignImport = (CallConv,Maybe Safety,Maybe String)
> data CallConv =
>   CallConvPrimitive | CallConvCCall | CallConvRawCall
>   deriving (Eq,Show)
> data Safety = Unsafe | Safe deriving (Eq,Show)
> data Trust = Suspect | Trust deriving (Eq,Show)
> data FreeVar a = FreeVar a Ident deriving (Eq,Show)

\end{verbatim}
\paragraph{Module interfaces}
Interface declarations are restricted to type declarations and signatures.
\begin{verbatim}

> data Interface =
>   Interface ModuleIdent [IImportDecl] [IDecl]
>   deriving (Eq,Show)

> data IImportDecl = IImportDecl Position ModuleIdent deriving (Eq,Show)

> data IDecl =
>     IInfixDecl Position Infix Integer QualIdent
>   | HidingDataDecl Position QualIdent (Maybe KindExpr) [Ident]
>   | IDataDecl Position [ClassAssert] QualIdent (Maybe KindExpr) [Ident]
>               [ConstrDecl] [Ident]
>   | INewtypeDecl Position [ClassAssert] QualIdent (Maybe KindExpr) [Ident]
>                  NewConstrDecl [Ident]
>   | ITypeDecl Position QualIdent (Maybe KindExpr) [Ident] TypeExpr
>   | HidingClassDecl Position [ClassAssert] QualIdent (Maybe KindExpr) Ident
>   | IClassDecl Position [ClassAssert] QualIdent (Maybe KindExpr) Ident
>                [IMethodDecl] [Ident]
>   | IInstanceDecl Position [ClassAssert] QualIdent TypeExpr
>                   (Maybe ModuleIdent) [(Ident,Integer)]
>   | IFunctionDecl Position QualIdent (Maybe Integer) QualTypeExpr
>   deriving (Eq,Show)

> data IMethodDecl =
>   IMethodDecl Position Ident (Maybe Integer) QualTypeExpr
>   deriving (Eq,Show)

\end{verbatim}
\paragraph{Kinds}
\begin{verbatim}

> data KindExpr = Star | ArrowKind KindExpr KindExpr deriving (Eq,Show)

\end{verbatim}
\paragraph{Types}
\begin{verbatim}

> data QualTypeExpr = QualTypeExpr [ClassAssert] TypeExpr deriving (Eq,Show)
> data ClassAssert = ClassAssert QualIdent TypeExpr deriving (Eq,Show)
> data TypeExpr =
>     ConstructorType QualIdent
>   | VariableType Ident
>   | TupleType [TypeExpr]
>   | ListType TypeExpr
>   | ArrowType TypeExpr TypeExpr
>   | ApplyType TypeExpr TypeExpr
>   deriving (Eq,Show)

\end{verbatim}
\paragraph{Functions}
\begin{verbatim}

> data Equation a = Equation Position (Lhs a) (Rhs a) deriving (Eq,Show)
> data Lhs a =
>     FunLhs Ident [ConstrTerm a]
>   | OpLhs (ConstrTerm a) Ident (ConstrTerm a)
>   | ApLhs (Lhs a) [ConstrTerm a]
>   deriving (Eq,Show)
> data Rhs a =
>     SimpleRhs Position (Expression a) [Decl a]
>   | GuardedRhs [CondExpr a] [Decl a]
>   deriving (Eq,Show)
> data CondExpr a =
>   CondExpr Position (Expression a) (Expression a)
>   deriving (Eq,Show)

\end{verbatim}
\paragraph{Literals}
\begin{verbatim}

> data Literal =
>     Char Char                         -- should be Int to handle Unicode
>   | Integer Integer
>   | Rational Rational
>   | String String                     -- should be [Int] to handle Unicode
>   deriving Show

> instance Eq Literal where
>   Char c1 == Char c2 = c1 == c2
>   Integer i1 == Integer i2 = i1 == i2
>   Integer i == Rational r = fromInteger i == r
>   Rational r == Integer i = r == fromInteger i
>   Rational r1 == Rational r2 = r1 == r2
>   String s1 == String s2 = s1 == s2
>   _ == _ = False

\end{verbatim}
\paragraph{Patterns}
Note that the (type) attributes of constructor, function, and infix
patterns will apply to the whole pattern and not to the pattern's
constructor or function itself. For that reason we only use a fixed
attribute for the operator of an infix pattern. List patterns carry an
attribute in order to accommodate the empty list.

\ToDo{Use \texttt{ConstructorPattern qNilId} to represent the empty
  list? If so, the attribute can be omitted from list patterns.}
\begin{verbatim}

> data ConstrTerm a =
>     LiteralPattern a Literal
>   | NegativePattern a Literal
>   | VariablePattern a Ident
>   | ConstructorPattern a QualIdent [ConstrTerm a]
>   | FunctionPattern a QualIdent [ConstrTerm a]
>   | InfixPattern a (ConstrTerm a) (InfixOp (){-sic!-}) (ConstrTerm a)
>   | ParenPattern (ConstrTerm a)
>   | RecordPattern a QualIdent [Field (ConstrTerm a)]
>   | TuplePattern [ConstrTerm a]
>   | ListPattern a [ConstrTerm a]
>   | AsPattern Ident (ConstrTerm a)
>   | LazyPattern (ConstrTerm a)
>   deriving (Eq,Show)

\end{verbatim}
\paragraph{Expressions}
Note that the empty list expression carries an attribute in order to
accommodate the empty list.

\ToDo{Use \texttt{Constructor qNilId} to represent the empty list? If
  so, the attribute can be omitted from list expressions.}
\begin{verbatim}

> data Expression a =
>     Literal a Literal
>   | Variable a QualIdent
>   | Constructor a QualIdent
>   | Paren (Expression a)
>   | Typed (Expression a) QualTypeExpr
>   | Record a QualIdent [Field (Expression a)]
>   | RecordUpdate (Expression a) [Field (Expression a)]
>   | Tuple [Expression a]
>   | List a [Expression a]
>   | ListCompr (Expression a) [Statement a]
>   | EnumFrom (Expression a)
>   | EnumFromThen (Expression a) (Expression a)
>   | EnumFromTo (Expression a) (Expression a)
>   | EnumFromThenTo (Expression a) (Expression a) (Expression a)
>   | UnaryMinus (Expression a)
>   | Apply (Expression a) (Expression a)
>   | InfixApply (Expression a) (InfixOp a) (Expression a)
>   | LeftSection (Expression a) (InfixOp a)
>   | RightSection (InfixOp a) (Expression a)
>   | Lambda Position [ConstrTerm a] (Expression a)
>   | Let [Decl a] (Expression a)
>   | Do [Statement a] (Expression a)
>   | IfThenElse (Expression a) (Expression a) (Expression a)
>   | Case (Expression a) [Alt a]
>   | Fcase (Expression a) [Alt a]
>   deriving (Eq,Show)

> data Field a = Field QualIdent a deriving (Eq,Show)

> data InfixOp a =
>     InfixOp a QualIdent
>   | InfixConstr a QualIdent
>   deriving (Eq,Show)

> data Statement a =
>     StmtExpr (Expression a)
>   | StmtBind Position (ConstrTerm a) (Expression a)
>   | StmtDecl [Decl a]
>   deriving (Eq,Show)

> data Alt a = Alt Position (ConstrTerm a) (Rhs a) deriving (Eq,Show)

\end{verbatim}
\paragraph{Goals}
A goal is equivalent to an unconditional right hand side of an equation.
\begin{verbatim}

> data Goal a = Goal Position (Expression a) [Decl a] deriving (Eq,Show)

\end{verbatim}
\paragraph{Attributes}
The abstract syntax tree is a functor with respect to its attributes.
\begin{verbatim}

> instance Functor Module where
>   fmap f (Module m es is ds) = Module m es is (map (fmap f) ds)

> instance Functor TopDecl where
>   fmap _ (DataDecl p cx tc tvs cs clss) = DataDecl p cx tc tvs cs clss
>   fmap _ (NewtypeDecl p cx tc tvs nc clss) = NewtypeDecl p cx tc tvs nc clss
>   fmap _ (TypeDecl p tc tvs ty) = TypeDecl p tc tvs ty
>   fmap f (ClassDecl p cx cls tv ds) = ClassDecl p cx cls tv (map (fmap f) ds)
>   fmap f (InstanceDecl p cx cls ty ds) =
>     InstanceDecl p cx cls ty (map (fmap f) ds)
>   fmap _ (DefaultDecl p tys) = DefaultDecl p tys
>   fmap f (BlockDecl d) = BlockDecl (fmap f d)

> instance Functor Decl where
>   fmap _ (InfixDecl p fix pr ops) = InfixDecl p fix pr ops
>   fmap _ (TypeSig p fs ty) = TypeSig p fs ty
>   fmap f (FunctionDecl p a f' eqs) =
>     FunctionDecl p (f a) f' (map (fmap f) eqs)
>   fmap f (ForeignDecl p fi a f' ty) = ForeignDecl p fi (f a) f' ty
>   fmap f (PatternDecl p t rhs) = PatternDecl p (fmap f t) (fmap f rhs)
>   fmap f (FreeDecl p vs) = FreeDecl p (map (fmap f) vs)
>   fmap _ (TrustAnnot p tr fs) = TrustAnnot p tr fs

> instance Functor FreeVar where
>   fmap f (FreeVar a v) = FreeVar (f a) v

> instance Functor Equation where
>   fmap f (Equation p lhs rhs) = Equation p (fmap f lhs) (fmap f rhs)

> instance Functor Lhs where
>   fmap f (FunLhs f' ts) = FunLhs f' (map (fmap f) ts)
>   fmap f (OpLhs t1 op t2) = OpLhs (fmap f t1) op (fmap f t2)
>   fmap f (ApLhs lhs ts) = ApLhs (fmap f lhs) (map (fmap f) ts)

> instance Functor Rhs where
>   fmap f (SimpleRhs p e ds) = SimpleRhs p (fmap f e) (map (fmap f) ds)
>   fmap f (GuardedRhs es ds) = GuardedRhs (map (fmap f) es) (map (fmap f) ds)

> instance Functor CondExpr where
>   fmap f (CondExpr p g e) = CondExpr p (fmap f g) (fmap f e)

> instance Functor ConstrTerm where
>   fmap f (LiteralPattern a l) = LiteralPattern (f a) l
>   fmap f (NegativePattern a l) = NegativePattern (f a) l
>   fmap f (VariablePattern a v) = VariablePattern (f a) v
>   fmap f (ConstructorPattern a c ts) =
>     ConstructorPattern (f a) c (map (fmap f) ts)
>   fmap f (FunctionPattern a f' ts) =
>     FunctionPattern (f a) f' (map (fmap f) ts)
>   fmap f (InfixPattern a t1 op t2) =
>     InfixPattern (f a) (fmap f t1) op (fmap f t2)
>   fmap f (ParenPattern t) = ParenPattern (fmap f t)
>   fmap f (RecordPattern a c fs) =
>     RecordPattern (f a) c (map (fmap (fmap f)) fs)
>   fmap f (TuplePattern ts) = TuplePattern (map (fmap f) ts)
>   fmap f (ListPattern a ts) = ListPattern (f a) (map (fmap f) ts)
>   fmap f (AsPattern v t) = AsPattern v (fmap f t)
>   fmap f (LazyPattern t) = LazyPattern (fmap f t)

> instance Functor Expression where
>   fmap f (Literal a l) = Literal (f a) l
>   fmap f (Variable a v) = Variable (f a) v
>   fmap f (Constructor a c) = Constructor (f a) c
>   fmap f (Paren e) = Paren (fmap f e)
>   fmap f (Typed e ty) = Typed (fmap f e) ty
>   fmap f (Record a c fs) = Record (f a) c (map (fmap (fmap f)) fs)
>   fmap f (RecordUpdate e fs) =
>     RecordUpdate (fmap f e) (map (fmap (fmap f)) fs)
>   fmap f (Tuple es) = Tuple (map (fmap f) es)
>   fmap f (List a es) = List (f a) (map (fmap f) es)
>   fmap f (ListCompr e qs) = ListCompr (fmap f e) (map (fmap f) qs)
>   fmap f (EnumFrom e) = EnumFrom (fmap f e)
>   fmap f (EnumFromThen e1 e2) = EnumFromThen (fmap f e1) (fmap f e2)
>   fmap f (EnumFromTo e1 e2) = EnumFromTo (fmap f e1) (fmap f e2)
>   fmap f (EnumFromThenTo e1 e2 e3) =
>     EnumFromThenTo (fmap f e1) (fmap f e2) (fmap f e3)
>   fmap f (UnaryMinus e) = UnaryMinus (fmap f e)
>   fmap f (Apply e1 e2) = Apply (fmap f e1) (fmap f e2)
>   fmap f (InfixApply e1 op e2) =
>     InfixApply (fmap f e1) (fmap f op) (fmap f e2)
>   fmap f (LeftSection e op) = LeftSection (fmap f e) (fmap f op)
>   fmap f (RightSection op e) = RightSection (fmap f op) (fmap f e)
>   fmap f (Lambda p ts e) = Lambda p (map (fmap f) ts) (fmap f e)
>   fmap f (Let ds e) = Let (map (fmap f) ds) (fmap f e)
>   fmap f (Do sts e) = Do (map (fmap f) sts) (fmap f e)
>   fmap f (IfThenElse e1 e2 e3) =
>     IfThenElse (fmap f e1) (fmap f e2) (fmap f e3)
>   fmap f (Case e as) = Case (fmap f e) (map (fmap f) as)
>   fmap f (Fcase e as) = Fcase (fmap f e) (map (fmap f) as)

> instance Functor InfixOp where
>   fmap f (InfixOp a op) = InfixOp (f a) op
>   fmap f (InfixConstr a op) = InfixConstr (f a) op

> instance Functor Statement where
>   fmap f (StmtExpr e) = StmtExpr (fmap f e)
>   fmap f (StmtBind p t e) = StmtBind p (fmap f t) (fmap f e)
>   fmap f (StmtDecl ds) = StmtDecl (map (fmap f) ds)

> instance Functor Alt where
>   fmap f (Alt p t rhs) = Alt p (fmap f t) (fmap f rhs)

> instance Functor Field where
>   fmap f (Field l x) = Field l (f x)

> instance Functor Goal where
>   fmap f (Goal p e ds) = Goal p (fmap f e) (map (fmap f) ds)

\end{verbatim}
