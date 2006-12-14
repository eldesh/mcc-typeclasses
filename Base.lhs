% -*- LaTeX -*-
% $Id: Base.lhs 2045 2006-12-14 12:43:17Z wlux $
%
% Copyright (c) 1999-2006, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Base.lhs}
\section{Common Definitions for the Compiler}
The module \texttt{Base} provides definitions that are commonly used
in various phases of the compiler.
\begin{verbatim}

> module Base(module Base,module Ident,module Position,module Types,
>             module CurrySyntax) where
> import Ident
> import Position
> import CurrySyntax
> import Types
> import Env
> import TopEnv
> import NestEnv
> import List
> import Maybe
> import Monad
> import Set

\end{verbatim}
\paragraph{Interfaces}
The compiler maintains a global environment containing all interfaces
imported directly or indirectly into the current module.
\begin{verbatim}

> type ModuleEnv = Env ModuleIdent Interface

> bindModule :: Interface -> ModuleEnv -> ModuleEnv
> bindModule (Interface m is ds) = bindEnv m (Interface m is ds)

\end{verbatim}
\paragraph{Type constructors and type classes}
For all defined types and type classes, the compiler must maintain
kind information. At present, the compiler does not support higher
order type classes. Therefore, its type language is first order and
the only information that must be recorded is the arity of each type.
For algebraic data types and renaming types, the compiler also records
all data constructors belonging to that type, for alias types the
expanded right hand side type expression is saved, and for type
classes the names of their super classes and the type class methods
are saved. No kind information is saved for type classes because only
single parameter type classes are supported and instance types must
have kind $\ast$. The list of super classes contains all direct and
indirect super classes and is always sorted by the names of the super
classes. Including \emph{all} super classes is necessary because
looking up indirect super classes in the type constructor environment
may be impossible for the names of the super classes may be ambiguous
or not in scope at all. Type classes are recorded in the type
constructor environment because type constructors and type classes
share a common name space.

\ToDo{Might also sort methods of a type class because their order is
  not relevant.}

Importing and exporting algebraic data types and renaming types is
complicated by the fact that the constructors of the type may be
(partially) hidden in the interface. This facilitates the definition
of abstract data types. An abstract type is always represented as a
data type without constructors in the interface regardless of whether
it is defined as a data type or as a renaming type. When only some
constructors of a data type are hidden, those constructors are
replaced by underscores in the interface. Similarly, it is possible to
hide some or all methods of a type class. The hidden methods are
replaced by underscores as well.
\begin{verbatim}

> type TCEnv = TopEnv TypeInfo

> data TypeInfo = DataType QualIdent Int [Maybe Ident]
>               | RenamingType QualIdent Int Ident
>               | AliasType QualIdent Int Type
>               | TypeClass QualIdent [QualIdent] [Maybe Ident]
>               deriving Show

> instance Entity TypeInfo where
>   origName (DataType tc _ _) = tc
>   origName (RenamingType tc _ _) = tc
>   origName (AliasType tc _ _) = tc
>   origName (TypeClass cls _ _) = cls
>   merge (DataType tc1 n cs1) (DataType tc2 _ cs2)
>     | tc1 == tc2 = Just (DataType tc1 n (mergeData cs1 cs2))
>     where mergeData cs1 cs2
>             | null cs1 = cs2
>             | null cs2 = cs1
>             | otherwise = zipWith mplus cs1 cs2
>   merge (DataType tc1 n _) (RenamingType tc2 _ nc)
>     | tc1 == tc2 = Just (RenamingType tc1 n nc)
>   merge (RenamingType tc1 n nc) (DataType tc2 _ _)
>     | tc1 == tc2 = Just (RenamingType tc1 n nc)
>   merge (RenamingType tc1 n nc) (RenamingType tc2 _ _)
>     | tc1 == tc2 = Just (RenamingType tc1 n nc)
>   merge (AliasType tc1 n ty) (AliasType tc2 _ _)
>     | tc1 == tc2 = Just (AliasType tc1 n ty)
>   merge (TypeClass cls1 clss fs1) (TypeClass cls2 _ fs2)
>     | cls1 == cls2 = Just (TypeClass cls1 clss (zipWith mplus fs1 fs2))
>   merge _ _ = Nothing

\end{verbatim}
The function \texttt{constrKind} returns the arity of a type
constructor from the type constructor environment and the function
\texttt{constructors} returns the names of the data and newtype
constructors of a type. Both functions are supposed to be used only
after checking for undefined and ambiguous type identifiers and
therefore should not fail.
\begin{verbatim}

> constrKind :: QualIdent -> TCEnv -> Int
> constrKind tc tcEnv =
>   case qualLookupTopEnv tc tcEnv of
>     [DataType _ n _] -> n
>     [RenamingType _ n _] -> n
>     [AliasType _ n _] -> n
>     _ -> internalError ("constrKind " ++ show tc)

> constructors :: QualIdent -> TCEnv -> [Maybe Ident]
> constructors tc tcEnv =
>   case qualLookupTopEnv tc tcEnv of
>     [DataType _ _ cs] -> cs
>     [RenamingType _ _ c] -> [Just c]
>     [AliasType _ _ _] -> []
>     _ -> internalError ("constructors " ++ show tc)

> superClasses :: QualIdent -> TCEnv -> [QualIdent]
> superClasses cls clsEnv =
>   case qualLookupTopEnv cls clsEnv of
>     [TypeClass _ clss _] -> clss
>     _ -> internalError ("superClasses " ++ show cls)

> classMethods :: QualIdent -> TCEnv -> [Maybe Ident]
> classMethods cls clsEnv =
>   case qualLookupTopEnv cls clsEnv of
>     [TypeClass _ _ fs] -> fs
>     _ -> internalError ("classMethods " ++ show cls)

\end{verbatim}
A simpler environment is used for checking the syntax of type
expressions, where only the original names and the data constructors
or methods associated with each type and type class, respectively, are
needed. Since synonym types are treated differently in import and
export lists, we distinguish data and renaming types on one side and
synonym types on the other side.
\begin{verbatim}

> type TypeEnv = TopEnv TypeKind

> data TypeKind =
>     Data QualIdent [Ident]
>   | Alias QualIdent
>   | Class QualIdent [Ident]
>   deriving (Eq,Show)

> typeKind :: TypeInfo -> TypeKind
> typeKind (DataType tc _ cs) = Data tc (catMaybes cs)
> typeKind (RenamingType tc _ c) = Data tc [c]
> typeKind (AliasType tc _ _) = Alias tc
> typeKind (TypeClass cls _ fs) = Class cls (catMaybes fs)

> instance Entity TypeKind where
>   origName (Data tc _) = tc
>   origName (Alias tc) = tc
>   origName (Class cls _) = cls

\end{verbatim}
\paragraph{Function and constructor types}
In order to test type correctness of a module, the compiler needs to
determine the type of every data constructor, function, and variable
in the module. For the purpose of type checking, there is no need to
distinguish variables and functions. For all objects, their original
names and their types are saved.

Even though value declarations may be nested, the compiler uses a flat
environment for saving type information. This is possible because all
identifiers are renamed by the compiler before it starts computing type
information.
\begin{verbatim}

> type ValueEnv = TopEnv ValueInfo

> data ValueInfo = DataConstructor QualIdent TypeScheme
>                | NewtypeConstructor QualIdent TypeScheme
>                | Value QualIdent TypeScheme
>                deriving Show

> instance Entity ValueInfo where
>   origName (DataConstructor origName _) = origName
>   origName (NewtypeConstructor origName _) = origName
>   origName (Value origName _) = origName

> bindFun :: ModuleIdent -> Ident -> TypeScheme -> ValueEnv -> ValueEnv
> bindFun m f ty = bindTopEnv m f (Value (qualifyWith m f) ty)

> rebindFun :: ModuleIdent -> Ident -> TypeScheme -> ValueEnv -> ValueEnv
> rebindFun m f ty = rebindTopEnv m f (Value (qualifyWith m f) ty)

\end{verbatim}
The functions \texttt{conType}, \texttt{varType}, and \texttt{funType}
return the type of constructors, pattern variables, and variables in
expressions, respectively, from the type environment. They are
supposed to be used only after checking for duplicate and ambiguous
identifiers and therefore should not fail.

The function \texttt{varType} can handle ambiguous identifiers and
returns the first available type. This makes it possible to use
\texttt{varType} in order to determine the type of a locally defined
function even though the function's name may be ambiguous.
\begin{verbatim}

> conType :: QualIdent -> ValueEnv -> TypeScheme
> conType c tyEnv =
>   case qualLookupTopEnv c tyEnv of
>     [DataConstructor _ ty] -> ty
>     [NewtypeConstructor _ ty] -> ty
>     _ -> internalError ("conType " ++ show c)

> varType :: Ident -> ValueEnv -> TypeScheme
> varType v tyEnv =
>   case lookupTopEnv v tyEnv of
>     Value _ ty : _ -> ty
>     _ -> internalError ("varType " ++ show v)

> funType :: QualIdent -> ValueEnv -> TypeScheme
> funType f tyEnv =
>   case qualLookupTopEnv f tyEnv of
>     [Value _ ty] -> ty
>     _ -> internalError ("funType " ++ show f)

\end{verbatim}
The function \texttt{isNewtypeConstr} uses the value type environment
in order to distinguish data and newtype constructors.
\begin{verbatim}

> isNewtypeConstr :: ValueEnv -> QualIdent -> Bool
> isNewtypeConstr tyEnv c =
>   case qualLookupTopEnv c tyEnv of
>     [DataConstructor _ _] -> False
>     [NewtypeConstructor _ _] -> True
>     _ -> internalError ("isNewtypeConstr: " ++ show c)

\end{verbatim}
A simpler kind of environment is used for syntax checking of
expressions. We only distinguish constructors and variables here. A
nested environment is used for syntax checking because it is performed
before renaming. However, only the top-level of this environment is
used in order to check the export list of a module.
\begin{verbatim}

> type FunEnv = TopEnv ValueKind
> type VarEnv = NestEnv ValueKind

> data ValueKind = Constr QualIdent | Var QualIdent deriving (Eq,Show)

> valueKind :: ValueInfo -> ValueKind
> valueKind (DataConstructor c _) = Constr c
> valueKind (NewtypeConstructor c _) = Constr c
> valueKind (Value v _) = Var v

> instance Entity ValueKind where
>   origName (Constr c) = c
>   origName (Var x) = x

\end{verbatim}
\paragraph{Instances}
The compiler maintains information about defined instances in an
environment that maps $C$-$T$-pairs, which associate a type class
identifier and a type constructor identifier, onto the context of the
corresponding instance declaration. A flat environment is sufficient
because instances are visible globally and cannot be hidden. Instance
relationships are recorded only with the original names of the class
and type constructor involved.
\begin{verbatim}

> data CT = CT QualIdent QualIdent deriving (Eq,Ord,Show)

> type InstEnv = Env CT Context

\end{verbatim}
When checking for duplicate instance declarations, the compiler simply
uses a set of $C$-$T$ pairs, which is derived from the instance
environment by ignoring the instance contexts.

\ToDo{Augment the \texttt{Env} module by a function which returns the
  domain of an environment as a set.}
\begin{verbatim}

> type InstSet = Set CT

> instSet :: InstEnv -> InstSet
> instSet = fromListSet . map fst . envToList

\end{verbatim}
\paragraph{Operator precedences}
In order to parse infix expressions correctly, the compiler must know
the precedence and associativity of each operator. Operator
precedences are associated with entities and will be checked after
renaming. Nevertheless, we need to save precedences for ambiguous
names in order to handle them correctly while computing the exported
interface of a module.

If no fixity is assigned to an operator, it will be given the default
precedence 9 and assumed to be a left-associative operator.
\begin{verbatim}

> data OpPrec = OpPrec Infix Int deriving Eq

> instance Show OpPrec where
>   showsPrec _ (OpPrec fix p) = showString (assoc fix) . shows p
>     where assoc InfixL = "left "
>           assoc InfixR = "right "
>           assoc Infix  = "non-assoc "

> defaultP :: OpPrec
> defaultP = OpPrec InfixL 9

\end{verbatim}
Operator precedences that are different from the default are recorded
in the precedence environment. A top-level environment is sufficient
because precedences are checked after renaming.
\begin{verbatim}

> type PEnv = TopEnv PrecInfo

> data PrecInfo = PrecInfo QualIdent OpPrec deriving (Eq,Show)

> instance Entity PrecInfo where
>   origName (PrecInfo op _) = op

\end{verbatim}
\paragraph{Trusted functions}
The compiler collects trust annotations from the source code in an
environment. A simple environment mapping unqualified names onto
annotations is sufficient because trust annotations control how
function declarations are transformed when generating code for the
declarative debugger (cf.  Sect.~\ref{sec:dtrans}).
\begin{verbatim}

> type TrustEnv = Env Ident Trust

\end{verbatim}
\paragraph{Predefined types}
The unit and list data types must be predefined because the
declarations
\begin{verbatim}
data () = ()
data [] a = [] | a : [a]
\end{verbatim}
are not valid in Curry. The same is true for the -- potentially --
infinite number of tuple types. The corresponding types are available
in the environments \texttt{initTCEnv} and \texttt{initDCEnv}. In
addition, the precedence of the infix list constructor is available in
the environment \texttt{initPEnv}. The initial instance environment is
empty. The initial type constructor environment also includes a fake
arrow type constructor, whose purpose is to allow defining instances
for the type \verb|a -> b|.
\begin{verbatim}

> initPEnv :: PEnv
> initPEnv = predefTopEnv qConsId (PrecInfo qConsId (OpPrec InfixR 5)) emptyPEnv
>   where emptyPEnv = emptyTopEnv Nothing

> initTCEnv :: TCEnv
> initTCEnv = foldr (uncurry predefTC) emptyTCEnv predefTypes
>   where emptyTCEnv = emptyTopEnv (Just (map fst tuples))
>         predefTC (TypeConstructor tc tys) cs =
>           predefTopEnv tc (DataType tc (length tys) (map (Just . fst) cs))

> initIEnv :: InstEnv
> initIEnv = emptyEnv

> initDCEnv :: ValueEnv
> initDCEnv = foldr (uncurry predefDC) emptyDCEnv (concatMap snd predefTypes)
>   where emptyDCEnv = emptyTopEnv (Just (map snd tuples))
>         predefDC c ty = predefTopEnv c' (DataConstructor c' (polyType ty))
>           where c' = qualify c

> predefTypes :: [(Type,[(Ident,Type)])]
> predefTypes =
>   let a = typeVar 0; b = typeVar 1 in [
>     (unitType,   [(unitId,unitType)]),
>     (listType a, [(nilId,nilType a), (consId,consType a)]),
>     (fakeArrowType a b, [])
>   ]
>   where nilType a = listType a
>         consType a = TypeArrow a (TypeArrow (listType a) (listType a))
>         fakeArrowType a b = TypeConstructor qArrowId [a,b]

> tuples :: [(TypeInfo,ValueInfo)]
> tuples = map tupleInfo [2..]
>   where tvs = map typeVar [0..]
>         tupleInfo n =
>           (DataType c n [Just (unqualify c)],
>            DataConstructor c (ForAll n (tupleConstrType (take n tvs))))
>           where c = qTupleId n
>         tupleConstrType tys = qualType (foldr TypeArrow (tupleType tys) tys)

\end{verbatim}
\paragraph{Free and bound variables}
The compiler needs to compute the sets of free and bound variables for
various entities. We will devote three type classes to that purpose.
The \texttt{QualExpr} class is expected to take into account that it
is possible to use a qualified name for referring to a function
defined in the current module and therefore \emph{M.x} and $x$, where
$M$ is the current module name, should be considered the same name.
However, note that this is correct only after renaming all local
definitions, as \emph{M.x} always denotes an entity defined at the
top-level.

The \texttt{Decl} instance of \texttt{QualExpr} returns all free
variables on the right hand side, regardless of whether they are bound
on the left hand side. This is more convenient because declarations are
usually processed in a declaration group where the set of free
variables cannot be computed independently for each declaration.
\begin{verbatim}

> class Expr e where
>   fv :: e -> [Ident]
> class QualExpr e where
>   qfv :: ModuleIdent -> e -> [Ident]
> class QuantExpr e where
>   bv :: e -> [Ident]

> instance Expr e => Expr [e] where
>   fv = concat . map fv
> instance QualExpr e => QualExpr [e] where
>   qfv m = concat . map (qfv m)
> instance QuantExpr e => QuantExpr [e] where
>   bv = concat . map bv

> instance QualExpr (Decl a) where
>   qfv m (FunctionDecl _ _ eqs) = qfv m eqs
>   qfv m (PatternDecl _ _ rhs) = qfv m rhs
>   qfv _ _ = []

> instance QuantExpr (Decl a) where
>   bv (FunctionDecl _ f _) = [f]
>   bv (ForeignDecl _ _ _ f _) = [f]
>   bv (PatternDecl _ t _) = bv t
>   bv (FreeDecl _ vs) = vs
>   bv _ = []

> instance QualExpr (Equation a) where
>   qfv m (Equation _ lhs rhs) = filterBv lhs (qfv m rhs)

> instance QuantExpr (Lhs a) where
>   bv = bv . snd . flatLhs

> instance QualExpr (Rhs a) where
>   qfv m (SimpleRhs _ e ds) = filterBv ds (qfv m e ++ qfv m ds)
>   qfv m (GuardedRhs es ds) = filterBv ds (qfv m es ++ qfv m ds)

> instance QualExpr (CondExpr a) where
>   qfv m (CondExpr _ g e) = qfv m g ++ qfv m e

> instance QualExpr (Expression a) where
>   qfv _ (Literal _ _) = []
>   qfv m (Variable _ v) = maybe [] return (localIdent m v)
>   qfv _ (Constructor _ _) = []
>   qfv m (Paren e) = qfv m e
>   qfv m (Typed e _) = qfv m e
>   qfv m (Tuple es) = qfv m es
>   qfv m (List _ es) = qfv m es
>   qfv m (ListCompr e qs) = foldr (qfvStmt m) (qfv m e) qs
>   qfv m (EnumFrom e) = qfv m e
>   qfv m (EnumFromThen e1 e2) = qfv m e1 ++ qfv m e2
>   qfv m (EnumFromTo e1 e2) = qfv m e1 ++ qfv m e2
>   qfv m (EnumFromThenTo e1 e2 e3) = qfv m e1 ++ qfv m e2 ++ qfv m e3
>   qfv m (UnaryMinus e) = qfv m e
>   qfv m (Apply e1 e2) = qfv m e1 ++ qfv m e2
>   qfv m (InfixApply e1 op e2) = qfv m op ++ qfv m e1 ++ qfv m e2
>   qfv m (LeftSection e op) = qfv m op ++ qfv m e
>   qfv m (RightSection op e) = qfv m op ++ qfv m e
>   qfv m (Lambda ts e) = filterBv ts (qfv m e)
>   qfv m (Let ds e) = filterBv ds (qfv m ds ++ qfv m e)
>   qfv m (Do sts e) = foldr (qfvStmt m) (qfv m e) sts
>   qfv m (IfThenElse e1 e2 e3) = qfv m e1 ++ qfv m e2 ++ qfv m e3
>   qfv m (Case e alts) = qfv m e ++ qfv m alts

> qfvStmt :: ModuleIdent -> Statement a -> [Ident] -> [Ident]
> qfvStmt m st fvs = qfv m st ++ filterBv st fvs

> instance QualExpr (Statement a) where
>   qfv m (StmtExpr e) = qfv m e
>   qfv m (StmtDecl ds) = filterBv ds (qfv m ds)
>   qfv m (StmtBind t e) = qfv m e

> instance QualExpr (Alt a) where
>   qfv m (Alt _ t rhs) = filterBv t (qfv m rhs)

> instance QuantExpr (Statement a) where
>   bv (StmtExpr e) = []
>   bv (StmtBind t e) = bv t
>   bv (StmtDecl ds) = bv ds

> instance QualExpr (InfixOp a) where
>   qfv m op = qfv m (infixOp op)

> instance QuantExpr (ConstrTerm a) where
>   bv (LiteralPattern _ _) = []
>   bv (NegativePattern _ _) = []
>   bv (VariablePattern _ v) = [v | v /= anonId]
>   bv (ConstructorPattern _ c ts) = bv ts
>   bv (InfixPattern _ t1 op t2) = bv t1 ++ bv t2
>   bv (ParenPattern t) = bv t
>   bv (TuplePattern ts) = bv ts
>   bv (ListPattern _ ts) = bv ts
>   bv (AsPattern v t) = v : bv t
>   bv (LazyPattern t) = bv t

> instance Expr QualTypeExpr where
>   fv (QualTypeExpr _ ty) = fv ty

> instance Expr TypeExpr where
>   fv (ConstructorType _ tys) = fv tys
>   fv (VariableType tv) = [tv]
>   fv (TupleType tys) = fv tys
>   fv (ListType ty) = fv ty
>   fv (ArrowType ty1 ty2) = fv ty1 ++ fv ty2

> filterBv :: QuantExpr e => e -> [Ident] -> [Ident]
> filterBv e = filter (`notElemSet` fromListSet (bv e))

\end{verbatim}
\paragraph{Miscellany}
Error handling
\begin{verbatim}

> errorAt :: Monad m => Position -> String -> m a
> errorAt p msg = fail (atP p msg)

> internalError :: String -> a
> internalError what = error ("internal error: " ++ what)

\end{verbatim}
Name supply for the generation of (type) variable names.
\begin{verbatim}

> nameSupply :: [Ident]
> nameSupply = map mkIdent [c:showNum i | i <- [0..], c <- ['a'..'z']]
>   where showNum 0 = ""
>         showNum n = show n

\end{verbatim}
\ToDo{The \texttt{nameSupply} should respect the current case mode, 
i.e., use upper case for variables in Prolog mode.}

Here is a list of predicates identifying various kinds of
declarations. Note that type class declarations are considered type
declarations because type constructors and type classes share a common
name space.
\begin{verbatim}

> isTypeDecl, isClassDecl, isInstanceDecl, isBlockDecl :: TopDecl a -> Bool
> isTypeDecl (DataDecl _ _ _ _ _ _) = True
> isTypeDecl (NewtypeDecl _ _ _ _ _ _) = True
> isTypeDecl (TypeDecl _ _ _ _) = True
> isTypeDecl (ClassDecl _ _ _ _ _) = True {-sic!-}
> isTypeDecl (InstanceDecl _ _ _ _ _) = False
> isTypeDecl (BlockDecl _) = False
> isClassDecl (ClassDecl _ _ _ _ _) = True
> isClassDecl _ = False
> isInstanceDecl (InstanceDecl _ _ _ _ _) = True
> isInstanceDecl _ = False
> isBlockDecl (BlockDecl _) = True
> isBlockDecl _ = False

> isInfixDecl, isTypeSig, isFreeDecl :: Decl a -> Bool
> isTrustAnnot, isValueDecl :: Decl a -> Bool
> isInfixDecl (InfixDecl _ _ _ _) = True
> isInfixDecl _ = False
> isTypeSig (TypeSig _ _ _) = True
> isTypeSig (ForeignDecl _ _ _ _ _) = True
> isTypeSig _ = False
> isFreeDecl (FreeDecl _ _) = True
> isFreeDecl _ = False
> isTrustAnnot (TrustAnnot _ _ _) = True
> isTrustAnnot _ = False
> isValueDecl (FunctionDecl _ _ _) = True
> isValueDecl (ForeignDecl _ _ _ _ _) = True
> isValueDecl (PatternDecl _ _ _) = True
> isValueDecl (FreeDecl _ _) = True
> isValueDecl _ = False

> isMethodSig :: MethodDecl a -> Bool
> isMethodSig (MethodSig _ _ _) = True
> isMethodSig (MethodDecl _ _ _) = False

\end{verbatim}
The function \texttt{infixOp} converts an infix operator into an
expression.
\begin{verbatim}

> infixOp :: InfixOp a -> Expression a
> infixOp (InfixOp a op) = Variable a op
> infixOp (InfixConstr a op) = Constructor a op

\end{verbatim}
The function \texttt{duplicates} returns a list containing all
duplicate items from its input list. The result is a list of pairs
whose first element contains the first occurrence of a duplicate item
and whose second element contains a list of all remaining occurrences
of that item.
\begin{verbatim}

> duplicates :: Eq a => [a] -> [(a,[a])]
> duplicates [] = []
> duplicates (x:xs)
>   | null ys = duplicates xs
>   | otherwise = (x,ys) : duplicates zs
>   where (ys,zs) = partition (x ==) xs

\end{verbatim}
