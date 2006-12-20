% -*- LaTeX -*-
% $Id: CaseCheck.lhs 2052 2006-12-20 11:37:05Z wlux $
%
% Copyright (c) 2003-2006, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CaseCheck.lhs}
\section{Case Mode Warnings}
By default, Curry does not enforce capitalization conventions for
identifiers. However, the compiler supports four different case modes
and issues warnings when the selected case mode is not obeyed. The
four supported modes are (cf.\ Sect.~C.1 of~\cite{Hanus:Report}):
\begin{itemize}
\item \emph{Free mode}: No constraints on the case of identifiers.
\item \emph{Haskell mode}: Constructor names should start with an
  upper case letter, function and variable names with a lower case
  letter. In addition, data constructor symbol names should start with
  a colon and function symbol names should not start with a colon.
\item \emph{Prolog mode}: Variable names should start with an upper
  case letter and function and constructor names with a lower case
  letter. No constraints for function and constructor symbols.
\item \emph{G\"odel mode}: Variable names should start with a lower
  case letter and function and constructor names with an upper case
  letter. No constraints for function and constructor symbols.
\end{itemize}

In order to check identifier cases, the compiler collects and
categorizes all type and value identifiers defined in the module. We
recognize the following seven identifier categories:
\emph{TypeConstrId}, \emph{TypeClassId}, \emph{TypeVarId},
\emph{DataConstrId}, \emph{FunctionId}, \emph{MethodId}, and
\emph{VariableId}. At present, we do not check module names, even
though Haskell requires them to start with an upper case letter.
\begin{verbatim}

> module CaseCheck(caseCheck,caseCheckGoal) where
> import Base
> import Char
> import List
> import Options

> data Case =
>   UpperCase | LowerCase | ColonCase | NoColonCase
>   deriving (Eq,Show)
> data Category =
>     TypeConstrId
>   | TypeClassId
>   | TypeVarId
>   | DataConstrId
>   | FunctionId
>   | MethodId
>   | VariableId
>   deriving Show

> data Definition = D Position Category Ident

> caseCheck :: CaseMode -> Module a -> [String]
> caseCheck cm m = check cm (definitions m)

> caseCheckGoal :: CaseMode -> Goal a -> [String]
> caseCheckGoal cm g = check cm (goalDefinitions g)

> check :: CaseMode -> [Definition] -> [String]
> check FreeMode = const []
> check HaskellMode = checkWith haskellMode
> check PrologMode = checkWith prologMode
> check GoedelMode = checkWith goedelMode

> checkWith :: (Category -> [Case]) -> [Definition] -> [String]
> checkWith f names =
>   [atP p (modeWarning x c cm) | D p c x <- names,
>                                 let cm = mode x,
>                                 cm `notElem` f c]

\end{verbatim}
Each case mode defines the admissible modes for all identifier
categories.
\begin{verbatim}

> mode :: Ident -> Case
> mode x
>  | isUpper c = UpperCase
>  | isLower c = LowerCase
>  | c == ':' = ColonCase
>  | otherwise = NoColonCase
>  where (c:_) = name x

> haskellMode :: Category -> [Case]
> haskellMode TypeConstrId = [UpperCase]
> haskellMode TypeClassId = [UpperCase]
> haskellMode TypeVarId = [LowerCase]
> haskellMode DataConstrId = [UpperCase,ColonCase]
> haskellMode FunctionId = [LowerCase,NoColonCase]
> haskellMode MethodId = [LowerCase,NoColonCase]
> haskellMode VariableId = [LowerCase,NoColonCase]

> prologMode :: Category -> [Case]
> prologMode TypeConstrId = [LowerCase]
> prologMode TypeClassId = [LowerCase]
> prologMode TypeVarId = [UpperCase]
> prologMode DataConstrId = [LowerCase,ColonCase,NoColonCase]
> prologMode FunctionId = [LowerCase,ColonCase,NoColonCase]
> prologMode MethodId = [LowerCase,ColonCase,NoColonCase]
> prologMode VariableId = [UpperCase]

> goedelMode :: Category -> [Case]
> goedelMode TypeConstrId = [UpperCase]
> goedelMode TypeClassId = [LowerCase]
> goedelMode TypeVarId = [LowerCase]
> goedelMode DataConstrId = [UpperCase,ColonCase,NoColonCase]
> goedelMode FunctionId = [UpperCase,ColonCase,NoColonCase]
> goedelMode MethodId = [UpperCase,ColonCase,NoColonCase]
> goedelMode VariableId = [LowerCase]

\end{verbatim}
The usual traversal of the syntax tree is necessary in order to
collect all defined identifiers.
\begin{verbatim}

> definitions :: Module a -> [Definition]
> definitions (Module _ _ _ ds) = names noPosition ds []
>   where noPosition = error "noPosition"

> goalDefinitions :: Goal a -> [Definition]
> goalDefinitions (Goal p e ds) = names p ds (names p e [])

> class SyntaxTree a where
>   names :: Position -> a -> [Definition] -> [Definition]

> instance SyntaxTree a => SyntaxTree [a] where
>   names p xs ys = foldr (names p) ys xs

> instance SyntaxTree (TopDecl a) where
>   names _ (DataDecl p _ tc tvs cs _) xs = typeNames p tc tvs ++ names p cs xs
>   names _ (NewtypeDecl p _ tc tvs nc _) xs =
>     typeNames p tc tvs ++ names p nc xs
>   names _ (TypeDecl p tc tvs _) xs = typeNames p tc tvs ++ xs
>   names _ (ClassDecl p _ cls tv ds) xs =
>     D p TypeClassId cls : D p TypeVarId tv : names p ds xs
>   names _ (InstanceDecl p _ _ ty ds) xs = names p ty (names p ds xs)
>   names p (BlockDecl d) xs = names p d xs

> typeNames :: Position -> Ident -> [Ident] -> [Definition]
> typeNames p tc tvs =
>   D p TypeConstrId tc : map (D p TypeVarId) (filter (not . isAnonId) tvs)

> instance SyntaxTree ConstrDecl where
>   names _ (ConstrDecl p evs c _) xs = constrNames p evs c ++ xs
>   names _ (ConOpDecl p evs _ c _) xs = constrNames p evs c ++ xs

> instance SyntaxTree NewConstrDecl where
>   names _ (NewConstrDecl p c _) xs = constrNames p [] c ++ xs

> constrNames ::  Position -> [Ident] -> Ident -> [Definition]
> constrNames p evs c =
>   D p DataConstrId c : map (D p TypeVarId) (filter (not . isAnonId) evs)

> instance SyntaxTree QualTypeExpr where
>   names p (QualTypeExpr _ ty) = names p ty

> instance SyntaxTree TypeExpr where
>   names p ty xs =
>     map (D p TypeVarId) (nub (filter (not . isAnonId) (fv ty))) ++ xs

> instance SyntaxTree (MethodDecl a) where
>   names _ (MethodFixity _ _ _ _) xs = xs
>   names _ (MethodSig p fs _) xs = map (D p MethodId) fs ++ xs
>   names _ (MethodDecl p _ eqs) xs = names p eqs xs
>   names _ (TrustMethod _ _ _) xs = xs

> instance SyntaxTree (Decl a) where
>   names _ (InfixDecl _ _ _ _) xs = xs
>   names _ (TypeSig p _ ty) xs = names p ty xs
>   names _ (FunctionDecl p f eqs) xs = D p FunctionId f : names p eqs xs
>   names _ (ForeignDecl p _ _ f ty) xs = D p FunctionId f : names p ty xs
>   names _ (PatternDecl p t rhs) xs = names p t (names p rhs xs)
>   names _ (FreeDecl p vs) xs = map (D p VariableId) vs ++ xs
>   names _ (TrustAnnot _ _ _) xs = xs

> instance SyntaxTree (Equation a) where
>   names _ (Equation p lhs rhs) = names p lhs . names p rhs

> instance SyntaxTree (Lhs a) where
>   names p (FunLhs _ ts) = names p ts
>   names p (OpLhs t1 _ t2) = names p t1 . names p t2
>   names p (ApLhs lhs ts) = names p lhs . names p ts

> instance SyntaxTree (Rhs a) where
>   names _ (SimpleRhs p e ds) = names p ds . names p e
>   names p (GuardedRhs es ds) = names p ds . names p es

> instance SyntaxTree (ConstrTerm a) where
>   names _ (LiteralPattern _ _) xs = xs
>   names _ (NegativePattern _ _) xs = xs
>   names p (VariablePattern _ v) xs
>     | isAnonId v = xs
>     | otherwise = D p VariableId v : xs
>   names p (ConstructorPattern _ _ ts) xs = names p ts xs
>   names p (InfixPattern _ t1 _ t2) xs = names p t1 (names p t2 xs)
>   names p (ParenPattern t) xs = names p t xs
>   names p (TuplePattern ts) xs = names p ts xs
>   names p (ListPattern _ ts) xs = names p ts xs
>   names p (AsPattern v t) xs = D p VariableId v : names p t xs
>   names p (LazyPattern t) xs = names p t xs

> instance SyntaxTree (CondExpr a) where
>   names _ (CondExpr p g e) = names p g . names p e

> instance SyntaxTree (Expression a) where
>   names _ (Literal _ _) = id
>   names _ (Variable _ _) = id
>   names _ (Constructor _ _) = id
>   names p (Paren e) = names p e
>   names p (Typed e ty) = names p e . names p ty
>   names p (Tuple es) = names p es
>   names p (List _ es) = names p es
>   names p (ListCompr e sts) = names p sts . names p e
>   names p (EnumFrom e) = names p e
>   names p (EnumFromThen e1 e2) = names p e1 . names p e2
>   names p (EnumFromTo e1 e2) = names p e1 . names p e2
>   names p (EnumFromThenTo e1 e2 e3) = names p e1 . names p e2 . names p e3
>   names p (UnaryMinus e) = names p e
>   names p (Apply e1 e2) = names p e1 . names p e2
>   names p (InfixApply e1 _ e2) = names p e1 . names p e2
>   names p (LeftSection e _) = names p e
>   names p (RightSection _ e) = names p e
>   names p (Lambda ts e) = names p ts . names p e
>   names p (Let ds e) = names p ds . names p e
>   names p (Do sts e) = names p sts . names p e
>   names p (IfThenElse e1 e2 e3) = names p e1 . names p e2 . names p e3
>   names p (Case e as) = names p e . names p as

> instance SyntaxTree (Statement a) where
>   names p (StmtExpr e) = names p e
>   names p (StmtDecl ds) = names p ds
>   names p (StmtBind t e) = names p t . names p e

> instance SyntaxTree (Alt a) where
>   names _ (Alt p t rhs) = names p t . names p rhs

> isAnonId :: Ident -> Bool
> isAnonId x = unRenameIdent x == anonId

\end{verbatim}
Warning messages.
\begin{verbatim}

> modeWarning :: Ident -> Category -> Case -> String
> modeWarning x c cm =
>   "Warning: name of " ++ kind c ++ " " ++ name x ++ " " ++ start cm

> kind :: Category -> String
> kind TypeConstrId = "type constructor"
> kind TypeClassId = "type class"
> kind TypeVarId = "type variable"
> kind DataConstrId = "data constructor"
> kind FunctionId = "function"
> kind MethodId = "type class method"
> kind VariableId = "variable"

> start :: Case -> String
> start UpperCase = "starts with an upper case letter"
> start LowerCase = "starts with a lower case letter"
> start ColonCase = "starts with a colon"
> start NoColonCase = "does not start with a colon"

\end{verbatim}
