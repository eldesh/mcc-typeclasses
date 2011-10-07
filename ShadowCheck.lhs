% -*- LaTeX -*-
% $Id: ShadowCheck.lhs 3056 2011-10-07 16:27:03Z wlux $
%
% Copyright (c) 2005-2011, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{ShadowCheck.lhs}
\section{Checking for Shadowing Definitions}
Besides unused variables, the compiler can also report local
definitions which shadow a declaration from an outer scope.

\ToDo{Report warnings for local type definitions that shadow imported
  type declarations and for type variables in type declarations that
  shadow type constructors.}
\begin{verbatim}

> module ShadowCheck(shadowCheck, shadowCheckGoal) where
> import Base
> import Curry
> import Interfaces
> import List
> import Map
> import Maybe
> import Options
> import Position

> infixl 1 &&&, >>>

> shadowCheck :: [Warn] -> ModuleEnv -> Module a -> [String]
> shadowCheck v mEnv (Module m _ is ds) =
>   report v $ shadow noPosition ds (const []) (imports mEnv is)
>   where noPosition = error "noPosition"

> shadowCheckGoal :: [Warn] -> ModuleEnv -> [ImportDecl] -> Goal a -> [String]
> shadowCheckGoal v mEnv is (Goal p e ds) =
>   report v $ shadow p (SimpleRhs p e ds) (const []) (imports mEnv is)

> report :: [Warn] -> [P (Ident,D)] -> [String]
> report ws
>   | WarnShadow `elem` ws = map format
>   | otherwise = const []

> format :: P (Ident,D) -> String
> format (P p (x,d)) = atP p ("Warning: " ++ name x ++ " shadows " ++ formatD d)

> formatD :: D -> String
> formatD (I ms) =
>   case nub ms of
>     [m] -> "import from module " ++ show m
>     [m1,m2] -> "imports from modules " ++ show m1 ++ " and " ++ show m2
>     ms' ->
>       "imports from modules " ++
>       concat (intersperse ", " (map show (init ms'))) ++ ", and " ++
>       show (last ms')
> formatD (L p') = "definition at " ++ show (p'{ file = "" })

\end{verbatim}
Since shadowing can be checked efficiently only with unrenamed
identifiers, we must be careful about the set of defined variables
that are visible when checking an expression. We implement the check
with a continuation passing style using functions that take a
continuation and a set of defined identifiers as input and return a
list of shadowing definitions. In order to combine continuations, we
introduce two combinators \verb|(>>>)| and \verb|(&&&)| where
$f\,$\verb|>>>|$\,g$ invokes $g$ with the set of variables augmented
by $f$ and $f\,$\verb|&&&|$\,g$ invokes both $f$ and $g$ with the same
set of defined variables.
\begin{verbatim}

> data D = I [ModuleIdent] | L Position
> type S = FM Ident D -> [P (Ident,D)]

> bindEnts :: [P Ident] -> S -> S
> bindEnts bvs k vs =
>   catMaybes [fmap (\d -> P p (x,d)) (lookupFM x vs) | P p x <- bvs] ++
>   k (foldr (uncurry addToFM) vs [(x,L p) | P p x <- bvs])

> (>>>), (&&&) :: (S -> S) -> (S -> S) -> S -> S
> f1 >>> f2 = \f gvs -> f1 (f2 f) gvs
> f1 &&& f2 = \f gvs -> f1 (const (f2 f gvs)) gvs

\end{verbatim}
Collecting shadowing identifiers is implemented by just another
traversal of the syntax tree. Note that method implementations in type
class and instance declarations do not define a new name and therefore
shadowing warnings are to be reported only for the right hand sides of
those method definitions.
\begin{verbatim}

> class SyntaxTree a where
>   shadow :: Position -> a -> S -> S
>   shadowGroup :: Position -> [a] -> S -> S
>   shadowGroup p = foldr ((&&&) . shadow p) id

> instance SyntaxTree a => SyntaxTree [a] where
>   shadow p = shadowGroup p

> instance SyntaxTree (TopDecl a) where
>   shadow _ (DataDecl _ _ _ _ _ _) = id
>   shadow _ (NewtypeDecl _ _ _ _ _ _) = id
>   shadow _ (TypeDecl _ _ _ _) = id
>   shadow _ (ClassDecl p _ _ _ ds) =
>     foldr (&&&) id [shadow p eqs | FunctionDecl p _ _ eqs <- ds]
>   shadow _ (InstanceDecl p _ _ _ ds) =
>     foldr (&&&) id [shadow p eqs | FunctionDecl p _ _ eqs <- ds]
>   shadow _ (DefaultDecl _ _) = id
>   shadow p (BlockDecl d) = shadow p d

>   shadowGroup p ds =
>     bindEnts (concatMap topEnts ds) >>> foldr ((&&&) . shadow p) id ds

> instance SyntaxTree (Decl a) where
>   shadow _ (InfixDecl _ _ _ _) = id
>   shadow _ (TypeSig _ _ _) = id
>   shadow _ (FunctionDecl p _ _ eqs) = shadow p eqs
>   shadow _ (ForeignDecl _ _ _ _ _) = id
>   shadow _ (PatternDecl p _ rhs) = shadow p rhs
>   shadow _ (FreeDecl _ _) = id
>   shadow _ (TrustAnnot _ _ _) = id
>
>   shadowGroup p ds =
>     bindEnts (concatMap vars ds) >>> foldr ((&&&) . shadow p) id ds

> instance SyntaxTree (Equation a) where
>   shadow _ (Equation p lhs rhs) = shadow p lhs >>> shadow p rhs

> instance SyntaxTree (Lhs a) where
>   shadow p lhs = bindEnts (map (P p) (bv lhs))

> instance SyntaxTree (ConstrTerm a) where
>   shadow p t = bindEnts (map (P p) (bv t))

> instance SyntaxTree (Rhs a) where
>   shadow _ (SimpleRhs p e ds) = shadow p ds >>> shadow p e
>   shadow p (GuardedRhs es ds) = shadow p ds >>> shadow p es

> instance SyntaxTree (CondExpr a) where
>   shadow _ (CondExpr p g e) = shadow p g &&& shadow p e

> instance SyntaxTree (Expression a) where
>   shadow _ (Literal _ _) = id
>   shadow _ (Variable _ _) = id
>   shadow _ (Constructor _ _) = id
>   shadow p (Paren e) = shadow p e
>   shadow p (Typed e _) = shadow p e
>   shadow p (Record _ _ fs) = shadow p fs
>   shadow p (RecordUpdate e fs) = shadow p e . shadow p fs
>   shadow p (Tuple es) = shadow p es
>   shadow p (List _ es) = shadow p es
>   shadow p (ListCompr e qs) = shadow p qs >>> shadow p e
>   shadow p (EnumFrom e) = shadow p e
>   shadow p (EnumFromThen e1 e2) = shadow p e1 &&& shadow p e2
>   shadow p (EnumFromTo e1 e2) = shadow p e1 &&& shadow p e2
>   shadow p (EnumFromThenTo e1 e2 e3) =
>     shadow p e1 &&& shadow p e2 &&& shadow p e3
>   shadow p (UnaryMinus e) = shadow p e
>   shadow p (Apply e1 e2) = shadow p e1 &&& shadow p e2
>   shadow p (InfixApply e1 _ e2) = shadow p e1 &&& shadow p e2
>   shadow p (LeftSection e _) = shadow p e
>   shadow p (RightSection _ e) = shadow p e
>   shadow _ (Lambda p ts e) = shadow p ts >>> shadow p e
>   shadow p (Let ds e) = shadow p ds >>> shadow p e
>   shadow p (Do sts e) = shadow p sts >>> shadow p e
>   shadow p (IfThenElse e1 e2 e3) =
>     shadow p e1 &&& shadow p e2 &&& shadow p e3
>   shadow p (Case e as) = shadow p e &&& shadow p as
>   shadow p (Fcase e as) = shadow p e &&& shadow p as

> instance SyntaxTree (Statement a) where
>   shadow p (StmtExpr e) = shadow p e
>   shadow _ (StmtBind p t e) = shadow p e &&& shadow p t
>   shadow p (StmtDecl ds) = shadow p ds

>   shadowGroup p = foldr ((>>>) . shadow p) id

> instance SyntaxTree (Alt a) where
>   shadow _ (Alt p t rhs) = shadow p t >>> shadow p rhs

> instance SyntaxTree a => SyntaxTree (Field a) where
>   shadow p (Field _ x) = shadow p x

\end{verbatim}
The functions \texttt{topEnts} and \texttt{vars} return the names of
the entities defined by a (top-level) declaration together with their
positions.
\begin{verbatim}

> topEnts :: TopDecl a -> [P Ident]
> topEnts (DataDecl _ _ _ _ cs _) = nub (concatMap ents cs)
>   where ents (ConstrDecl p _ _ c _) = [P p c]
>         ents (ConOpDecl p _ _ _ op _) = [P p op]
>         ents (RecordDecl p _ _ c fs) =
>           P p c : [P p l | FieldDecl p ls _ <- fs, l <- ls]
> topEnts (NewtypeDecl _ _ _ _ nc _) = ents nc
>   where ents (NewConstrDecl p c _) = [P p c]
>         ents (NewRecordDecl p c l _) = [P p c,P p l]
> topEnts (TypeDecl _ _ _ _) = []
> topEnts (ClassDecl _ _ _ _ ds) = [P p f | TypeSig p fs _ <- ds, f <- fs]
> topEnts (InstanceDecl _ _ _ _ _) = []
> topEnts (DefaultDecl _ _) = []
> topEnts (BlockDecl d) = vars d

> vars :: Decl a -> [P Ident]
> vars (InfixDecl _ _ _ _) = []
> vars (TypeSig _ _ _) = []
> vars (FunctionDecl p _ f _) = [P p f]
> vars (ForeignDecl p _ _ f _) = [P p f]
> vars (PatternDecl p t _) = map (P p) (bv t)
> vars (FreeDecl p vs) = map (P p) (bv vs)
> vars (TrustAnnot _ _ _) = []

\end{verbatim}
In order to report imported definitions that are shadowed by top-level
or local declarations, we process the import declarations of the
module. Since we consider only unqualified identifiers for shadowing
warnings we can ignore all qualified imports. Note that we collect the
import paths under which identifier is available, not the original
names of the imported entities.
\begin{verbatim}

> imports :: ModuleEnv -> [ImportDecl] -> FM Ident D
> imports mEnv is = foldr importModule zeroFM is
>   where importModule (ImportDecl _ m q _ is) xs =
>           foldr (importEnt m) xs (visible q is xs')
>           where xs' = ents (moduleInterface m mEnv)
>         importEnt m x xs =
>           addToFM x (I (m : maybe [] (\(I ms) -> ms) (lookupFM x xs))) xs
>         ents (Interface _ _ ds) = concatMap intfEnts ds

> visible :: Bool -> Maybe ImportSpec -> [Ident] -> [Ident]
> visible True _ = const []
> visible False Nothing = id
> visible False (Just (Importing _ is)) = const (foldr impEnts [] is)
> visible False (Just (Hiding _ is)) = filter (`notElem` foldr impEnts [] is)

> impEnts :: Import -> [Ident] -> [Ident]
> impEnts (Import x) = (x:)
> impEnts (ImportTypeWith _ xs) = (xs ++)

> intfEnts :: IDecl -> [Ident]
> intfEnts (IInfixDecl _ _ _ _) = []
> intfEnts (HidingDataDecl _ _ _ _) = []
> intfEnts (IDataDecl _ _ _ _ _ cs xs) =
>   filter (`notElem` xs) (concatMap ents cs)
>   where ents (ConstrDecl _ _ _ c _) = [c]
>         ents (ConOpDecl _ _ _ _ op _) = [op]
>         ents (RecordDecl _ _ _ c fs) =
>           c : [l | FieldDecl _ ls _ <- fs, l <- ls]
> intfEnts (INewtypeDecl _ _ _ _ _ nc xs) = filter (`notElem` xs) (ents nc)
>   where ents (NewConstrDecl _ c _) = [c]
>         ents (NewRecordDecl _ c l _) = [c,l]
> intfEnts (ITypeDecl _ _ _ _ _) = []
> intfEnts (HidingClassDecl _ _ _ _ _) = []
> intfEnts (IClassDecl _ _ _ _ _ ds fs) = filter (`notElem` fs) (map mthd ds)
>   where mthd (IMethodDecl _ f _ _) = f
> intfEnts (IInstanceDecl _ _ _ _ _ _) = []
> intfEnts (IFunctionDecl _ f _ _) = [unqualify f]

\end{verbatim}
