% -*- LaTeX -*-
% $Id: CurrySyntax.lhs 2418 2007-07-26 17:44:48Z wlux $
%
% Copyright (c) 1999-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CurrySyntax.lhs}
\section{The Parse Tree}
This module provides the necessary data structures to maintain the
parsed representation of a Curry program. The syntax tree carries
attributes for literals, variables, and constructors appearing in
patterns and expressions. At present, these attributes are used for
associating types with patterns and expressions after type inference.
\begin{verbatim}

> module CurrySyntax where
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
>     DataDecl Position [ClassAssert] Ident [Ident] [ConstrDecl] [QualIdent]
>   | NewtypeDecl Position [ClassAssert] Ident [Ident] NewConstrDecl [QualIdent]
>   | TypeDecl Position Ident [Ident] TypeExpr
>   | ClassDecl Position [ClassAssert] Ident Ident [MethodDecl a]
>   | InstanceDecl Position [ClassAssert] QualIdent TypeExpr [MethodDecl a]
>   | BlockDecl (Decl a)
>   deriving (Eq,Show)

> data ConstrDecl =
>     ConstrDecl Position [Ident] Ident [TypeExpr]
>   | ConOpDecl Position [Ident] TypeExpr Ident TypeExpr
>   deriving (Eq,Show)
> data NewConstrDecl = NewConstrDecl Position Ident TypeExpr deriving (Eq,Show)

> data MethodDecl a =
>     MethodFixity Position Infix (Maybe Int) [Ident]
>   | MethodSig Position [Ident] QualTypeExpr
>   | MethodDecl Position Ident [Equation a]
>   | TrustMethod Position Trust [Ident]
>   deriving (Eq,Show)
> data Decl a =
>     InfixDecl Position Infix (Maybe Int) [Ident]
>   | TypeSig Position [Ident] QualTypeExpr
>   | FunctionDecl Position Ident [Equation a]
>   | ForeignDecl Position CallConv (Maybe Safety) (Maybe String) Ident TypeExpr
>   | PatternDecl Position (ConstrTerm a) (Rhs a)
>   | FreeDecl Position [Ident]
>   | TrustAnnot Position Trust [Ident]
>   deriving (Eq,Show)

> data Infix = Infix | InfixL | InfixR deriving (Eq,Show)
> data CallConv =
>   CallConvPrimitive | CallConvCCall | CallConvRawCall
>   deriving (Eq,Show)
> data Safety = Unsafe | Safe deriving (Eq,Show)
> data Trust = Suspect | Trust deriving (Eq,Show)

> constr :: ConstrDecl -> Ident
> constr (ConstrDecl _ _ c _) = c
> constr (ConOpDecl _ _ _ op _) = op

> nconstr :: NewConstrDecl -> Ident
> nconstr (NewConstrDecl _ c _) = c

> methods :: MethodDecl a -> [Ident]
> methods (MethodFixity _ _ _ _) = []
> methods (MethodSig _ fs _) = fs
> methods (MethodDecl _ _ _) = []
> methods (TrustMethod _ _ _) = []

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
>   | HidingDataDecl Position QualIdent (Maybe KindExpr) [Ident]
>   | IDataDecl Position [ClassAssert] QualIdent (Maybe KindExpr) [Ident]
>               [Maybe ConstrDecl]
>   | INewtypeDecl Position [ClassAssert] QualIdent (Maybe KindExpr) [Ident]
>                  NewConstrDecl
>   | ITypeDecl Position QualIdent (Maybe KindExpr) [Ident] TypeExpr
>   | HidingClassDecl Position [ClassAssert] QualIdent (Maybe KindExpr) Ident
>   | IClassDecl Position [ClassAssert] QualIdent (Maybe KindExpr) Ident
>                [Maybe IMethodDecl]
>   | IInstanceDecl Position [ClassAssert] QualIdent TypeExpr
>                   (Maybe ModuleIdent)
>   | IFunctionDecl Position QualIdent (Maybe Int) QualTypeExpr
>   deriving (Eq,Show)

> data IMethodDecl = IMethodDecl Position Ident QualTypeExpr deriving (Eq,Show)

> imethod :: IMethodDecl -> Ident
> imethod (IMethodDecl _ f _) = f

\end{verbatim}
\paragraph{Kinds}
\begin{verbatim}

> data KindExpr = Star | ArrowKind KindExpr KindExpr deriving (Eq,Show)

\end{verbatim}
\paragraph{Types}
\begin{verbatim}

> data QualTypeExpr = QualTypeExpr [ClassAssert] TypeExpr deriving (Eq,Show)
> data ClassAssert = ClassAssert QualIdent Ident [TypeExpr] deriving (Eq,Show)
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

> eqnArity :: Equation a -> Int
> eqnArity (Equation _ lhs _) = length (snd (flatLhs lhs))

> flatLhs :: Lhs a -> (Ident,[ConstrTerm a])
> flatLhs lhs = flat lhs []
>   where flat (FunLhs f ts) ts' = (f,ts ++ ts')
>         flat (OpLhs t1 op t2) ts = (op,t1:t2:ts)
>         flat (ApLhs lhs ts) ts' = flat lhs (ts ++ ts')

\end{verbatim}
\paragraph{Literals}
\begin{verbatim}

> data Literal =
>     Char Char                         -- should be Int to handle Unicode
>   | Int Int
>   | Float Double
>   | String String                     -- should be [Int] to handle Unicode
>   deriving (Eq,Show)

\end{verbatim}
\paragraph{Patterns}
Note that the (type) attributes of constructor and infix patterns will
apply to the whole pattern an not to the pattern's constructor itself.
List patterns carry an attribute in order to accommodate the empty
list.

\ToDo{Use \texttt{ConstructorPattern qNilId} to represent the empty
  list? If so, the attribute can be omitted from list patterns.}
\begin{verbatim}

> data ConstrTerm a =
>     LiteralPattern a Literal
>   | NegativePattern a Literal
>   | VariablePattern a Ident
>   | ConstructorPattern a QualIdent [ConstrTerm a]
>   | InfixPattern a (ConstrTerm a) QualIdent (ConstrTerm a)
>   | ParenPattern (ConstrTerm a)
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
>   deriving (Eq,Show)

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

> opName :: InfixOp a -> QualIdent
> opName (InfixOp _ op) = op
> opName (InfixConstr _ c) = c

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
>   fmap f (BlockDecl d) = BlockDecl (fmap f d)

> instance Functor MethodDecl where
>   fmap _ (MethodFixity p fix pr ops) = MethodFixity p fix pr ops
>   fmap _ (MethodSig p fs ty) = MethodSig p fs ty
>   fmap f (MethodDecl p f' eqs) = MethodDecl p f' (map (fmap f) eqs)
>   fmap _ (TrustMethod p tr fs) = TrustMethod p tr fs

> instance Functor Decl where
>   fmap _ (InfixDecl p fix pr ops) = InfixDecl p fix pr ops
>   fmap _ (TypeSig p fs ty) = TypeSig p fs ty
>   fmap f (FunctionDecl p f' eqs) = FunctionDecl p f' (map (fmap f) eqs)
>   fmap _ (ForeignDecl p cc s ie f ty) = ForeignDecl p cc s ie f ty
>   fmap f (PatternDecl p t rhs) = PatternDecl p (fmap f t) (fmap f rhs)
>   fmap _ (FreeDecl p vs) = FreeDecl p vs
>   fmap _ (TrustAnnot p tr fs) = TrustAnnot p tr fs

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
>   fmap f (InfixPattern a t1 op t2) =
>     InfixPattern (f a) (fmap f t1) op (fmap f t2)
>   fmap f (ParenPattern t) = ParenPattern (fmap f t)
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

> instance Functor InfixOp where
>   fmap f (InfixOp a op) = InfixOp (f a) op
>   fmap f (InfixConstr a op) = InfixConstr (f a) op

> instance Functor Statement where
>   fmap f (StmtExpr e) = StmtExpr (fmap f e)
>   fmap f (StmtBind p t e) = StmtBind p (fmap f t) (fmap f e)
>   fmap f (StmtDecl ds) = StmtDecl (map (fmap f) ds)

> instance Functor Alt where
>   fmap f (Alt p t rhs) = Alt p (fmap f t) (fmap f rhs)

> instance Functor Goal where
>   fmap f (Goal p e ds) = Goal p (fmap f e) (map (fmap f) ds)

\end{verbatim}
