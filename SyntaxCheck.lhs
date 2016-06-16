% -*- LaTeX -*-
% $Id: SyntaxCheck.lhs 3225 2016-06-16 08:40:29Z wlux $
%
% Copyright (c) 1999-2015, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{SyntaxCheck.lhs}
\section{Syntax Checks}
After the type declarations have been checked, the compiler performs a
syntax check on the remaining declarations. This check disambiguates
nullary data constructors and variables, which cannot be done in the
parser because Curry -- in contrast to many other declarative
languages -- lacks a capitalization convention. In addition, this pass
checks for undefined as well as ambiguous value identifiers. Finally,
all (adjacent) equations of a function are merged into a single
definition.
\begin{verbatim}

> module SyntaxCheck(syntaxCheck,syntaxCheckGoal) where
> import Applicative
> import Base
> import Char
> import Curry
> import CurryPP
> import CurryUtils
> import Error
> import IdentInfo
> import List
> import Maybe
> import Monad
> import TopEnv
> import NestEnv
> import Position
> import Pretty
> import Utils

\end{verbatim}
In order to check patterns and expressions, the compiler maintains an
environment that records all known functions, data, and newtype
constructors. For each nested declaration group in the source code, a
new scope is opened in this environment. The functions
\texttt{syntaxCheck} and \texttt{syntaxCheckGoal} expect an
environment that is already initialized with the imported functions
and data and newtype constructors. First, the data and newtype
constructors defined in the current module are added to this
environment. Then, all declarations are checked within the resulting
environment and the declared functions and variables are added to
their respective scopes in the environment. The final top-level
environment is returned from \texttt{syntaxCheck} in order to be used
later for checking the optional export list of the current module.
\begin{verbatim}

> syntaxCheck :: ModuleIdent -> TypeEnv -> FunEnv -> [TopDecl a]
>             -> Error (FunEnv,[TopDecl a])
> syntaxCheck m tEnv env ds =
>   do
>     reportDuplicates duplicateData repeatedData cs
>     (env'',ds') <- checkTopDecls m tEnv cs ls env' ds
>     return (toplevelEnv env'',ds')
>   where env' = foldr (bindConstr m) (globalEnv env) cs
>         cs = concatMap constrs ds
>         ls = concatMap fieldLabels ds

> syntaxCheckGoal :: FunEnv -> Goal a -> Error (Goal a)
> syntaxCheckGoal env g = checkGoal (globalEnv env) g

> bindConstr :: ModuleIdent -> P Ident -> VarEnv -> VarEnv
> bindConstr m (P _ c) = globalBindNestEnv m c (Constr (qualifyWith m c))

> bindLabel :: ModuleIdent -> (P Ident,[Ident]) -> VarEnv -> VarEnv
> bindLabel m (P _ l,cs) =
>   globalBindNestEnv m l (Var (qualifyWith m l) (map (qualifyWith m) cs))

> bindFunc :: ModuleIdent -> P Ident -> VarEnv -> VarEnv
> bindFunc m (P _ f) = globalBindNestEnv m f (Var (qualifyWith m f) [])

> bindVar :: P Ident -> VarEnv -> VarEnv
> bindVar (P _ v) = localBindNestEnv v (Var (qualify v) [])

\end{verbatim}
In each declaration group, the compiler must first disambiguate
variable and data constructor identifiers on the left hand side so
that it can distinguish function and pattern declarations. For
instance, the declaration \texttt{Just x = Nothing} is syntactically
both a valid function declaration defining the function \texttt{Just}
and a pattern declaration matching the pattern \texttt{Just x} against
the expression \texttt{Nothing}. Since no pattern declarations are
allowed at the top-level of a module, the declaration is unambiguous
in the global scope. In a local declaration group, we always consider
the declaration a pattern declaration provided that the Prelude's
definition of data constructor \texttt{Just} is in scope.

The ambiguity is getting more subtle when infix operator declarations
and infix patterns are taken into account.\footnote{Infix constructors
  are an extension supported for compatibility with Haskell. The Curry
  report~\cite{Hanus:Report} knows only a single infix data
  constructor, the list constructor \texttt{:}.} Consider a
declaration \texttt{$t_1$ `op$_1$` $t_2$ $\dots$ $t_n$ `op$_n$` $t_n$
  = $e$}. If all operators $\texttt{op}_1, \dots, \texttt{op}_n$
except for a single operator $op_i$ denote a data constructor, this
declaration is considered a function declaration of \texttt{op$_i$}.
If more than one operator does not denote a data constructor, the
declaration is invalid and we arbitrarily choose the leftmost operator
as root of the left hand side. If all operators denote a data
constructor, the declaration is considered a pattern declaration, but
only in a local declaration group. At the top-level, we arbitrarily
choose the leftmost unqualified operator (if one exists) and consider
the declaration a function declaration of that operator. Ideally, the
choice of the left hand side's root operator should be based on the
relative precedences of the operators, but unfortunately these
precedences are not known during syntax checking\footnote{Note that
  this is a principal limitation. Since fixities are associated with
  entities and not identifiers, the fixity of an operator cannot be
  known before the compiler knows where the identifier is defined.}.
For some contrived examples our heuristics means that the compiler may
choose the wrong root, e.g.,
\begin{verbatim}
module A where { infixl 7 :/; data Rat a = a :/ a }
module M where
  import A
  infixl 1 :/; infix 4 :=
  data Assoc a b = a := b
  a := _ :/ b = a := b
\end{verbatim}
The last line of module \texttt{M} is supposed to define the operator
\verb|:/| and, in fact, the compiler would accept this declaration if
the import of module A where omitted. Unfortunately, the import
declaration brings a data constructor definition for \verb|:/| into
scope, which means that the compiler will -- wrongly -- consider the
leftmost unqualified operator, i.e., \verb|:=| the root of the left
hand side and therefore complain about the redefinition of that
operator. To avoid this error, the user has to add redundant
parentheses around the argument term \verb|a := _| or use the
qualified name \texttt{M.:=} for the first operator.

After disambiguating variable and data constructor identifiers, the
compiler merges adjacent equations for the same function into a single
definition. When a module's global declaration group is checked, the
compiler must be careful to preserve the order of type and value
declarations; otherwise it would fail to detect the error in the
following code fragment.
\begin{verbatim}
  f = 0
  data T = C
  f = 1
\end{verbatim}
Next, the compiler checks that there is a corresponding value
definition for every fixity declaration, type signature, and trust
annotation in this group and that there are no duplicate definitions.
Finally, each declaration of the group is checked.

Without function patterns it would be safe to report undefined data
constructors already during disambiguation because data constructors
can be defined only in top-level declarations and pattern declarations
are valid only in local declaration groups. However, a function
pattern in a pattern declaration might use a function defined in the
same declaration group, e.g.\ \texttt{let dup x = (x,x); (dup z) = e
  in z}.\footnote{The parentheses around \texttt{(dup z)} are
  necessary to make the declaration a pattern declaration.}
Therefore, we can report undefined identifiers only after determining
the bound identifiers of the current declaration group.

Note that fixity declarations for class methods can occur either at
the top-level of a module or in the class declaration itself
(cf.\ Sect.~4.4.2 of the revised Haskell'98
report~\cite{PeytonJones03:Haskell}). In order to detect duplicate
fixity declarations for class methods, the relevant top-level fixity
declarations are passed to \texttt{checkMethodDecls}.
\begin{verbatim}

> checkTopDecls :: ModuleIdent -> TypeEnv -> [P Ident] -> [(P Ident,[Ident])]
>               -> VarEnv -> [TopDecl a] -> Error (VarEnv,[TopDecl a])
> checkTopDecls m tEnv cs ls env ds =
>   do
>     ds' <- liftA joinTopEquations (mapA (disambTopDecl env) ds)
>     env'' <- checkDeclVars (bindFunc m) xs (concatMap mthds ds') env'
>                            [d | BlockDecl d <- ds']
>     ds'' <- mapA (checkTopDecl tEnv env'' ops) ds'
>     return (env'',ds'')
>   where ops = [P p op | BlockDecl (InfixDecl p _ _ ops) <- ds, op <- ops]
>         env' = foldr (bindLabel m) env ls
>         xs = mergeBy comparePos cs (map fst ls)

> disambTopDecl :: VarEnv -> TopDecl a -> Error (TopDecl a)
> disambTopDecl _ (DataDecl p cx tc tvs cs clss) =
>   return (DataDecl p cx tc tvs cs clss)
> disambTopDecl _ (NewtypeDecl p cx tc tvs nc clss) =
>   return (NewtypeDecl p cx tc tvs nc clss)
> disambTopDecl _ (TypeDecl p tc tvs ty) = return (TypeDecl p tc tvs ty)
> disambTopDecl _ (ClassDecl p cx cls tv ds) = return (ClassDecl p cx cls tv ds)
> disambTopDecl _ (InstanceDecl p cx cls ty ds) =
>   return (InstanceDecl p cx cls ty ds)
> disambTopDecl _ (DefaultDecl p tys) = return (DefaultDecl p tys)
> disambTopDecl env (BlockDecl d) = liftA BlockDecl (disambBlockDecl env d)

> disambBlockDecl :: VarEnv -> Decl a -> Error (Decl a)
> disambBlockDecl _ (InfixDecl p fix pr ops) = return (InfixDecl p fix pr ops)
> disambBlockDecl _ (TypeSig p vs ty) = return (TypeSig p vs ty)
> disambBlockDecl env (FunctionDecl p a _ [Equation p' lhs rhs]) =
>   case disambLhs env a lhs of
>     Left (a',f',lhs') -> return (funDecl a' f' lhs')
>     Right t' ->
>       case msum (map toFunLhs (terms t')) of
>         Just (f',lhs') -> return (funDecl a f' lhs')
>         Nothing -> errorAt p noToplevelPattern
>   where funDecl a f lhs = FunctionDecl p a f [Equation p' lhs rhs]
> disambBlockDecl _ (ForeignDecl p fi a f ty) = return (ForeignDecl p fi a f ty)
> --disambBlockDecl _ (PatternDecl p _ _) = errorAt p noToplevelPattern
> --disambBlockDecl _ (FreeDecl p _) = errorAt p noToplevelFree
> disambBlockDecl _ (TrustAnnot p t fs) = return (TrustAnnot p t fs)

> terms :: ConstrTerm a -> [ConstrTerm a]
> terms t = t :
>   case t of
>     InfixPattern a1 t1 op1 (InfixPattern a2 t2 op2 t3) ->
>       terms (InfixPattern a2 (InfixPattern a1 t1 op1 t2) op2 t3)
>     _ -> []

> toFunLhs :: ConstrTerm a -> Maybe (Ident,Lhs a)
> toFunLhs t =
>   case t of
>     VariablePattern _ v -> Just (v,FunLhs v [])
>     ConstructorPattern _ c ts -> funLhs (\f -> FunLhs f ts) c
>     InfixPattern _ t1 (InfixConstr _ op) t2 -> funLhs (\f -> OpLhs t1 f t2) op
>     _ -> Nothing
>   where funLhs lhs c = maybe (Just (f,lhs f)) (const Nothing) m
>           where (m,f) = splitQualIdent c

> joinTopEquations :: [TopDecl a] -> [TopDecl a]
> joinTopEquations [] = []
> joinTopEquations (d : ds)
>   | isBlockDecl d =
>       map BlockDecl (joinEquations [d | BlockDecl d <- d:ds']) ++
>       joinTopEquations ds''
>   | otherwise = d : joinTopEquations ds
>   where (ds',ds'') = span isBlockDecl ds

> checkTopDecl :: TypeEnv -> VarEnv -> [P Ident] -> TopDecl a
>                 -> Error (TopDecl a)
> checkTopDecl _ _ _ (DataDecl p cx tc tvs cs clss) =
>   mapA_ checkDeclLabels cs >> return (DataDecl p cx tc tvs cs clss)
> checkTopDecl _ _ _ (NewtypeDecl p cx tc tvs nc clss) =
>   return (NewtypeDecl p cx tc tvs nc clss)
> checkTopDecl _ _ _ (TypeDecl p tc tvs ty) = return (TypeDecl p tc tvs ty)
> checkTopDecl _ env ops (ClassDecl p cx cls tv ds) =
>   liftA (ClassDecl p cx cls tv)
>         (checkMethodDecls env (qualify cls) (filter (`elem` fs) ops) fs ds)
>   where fs = mthds (ClassDecl p cx cls tv ds)
> checkTopDecl tEnv env _ (InstanceDecl p cx cls ty ds) =
>   liftA (InstanceDecl p cx cls ty) (checkMethodDecls env cls [] fs ds)
>   where fs = map (P p) (classMthds cls tEnv)
> checkTopDecl _ _ _ (DefaultDecl p tys) = return (DefaultDecl p tys)
> checkTopDecl _ env _ (BlockDecl d) = liftA BlockDecl (checkDecl env d)

\end{verbatim}
The compiler checks field labels in data type declarations twice
because field labels must be globally unique and also must be unique
for each constructor declaration, but the same label may be used in
different constructors of the same data type. Global uniqueness is
checked in function \texttt{checkDeclVars}, which also ensures that
there are no conflicts between field labels and global functions,
whereas the function \texttt{checkDeclLabels} below checks that each
field label occurs at most once in a particular data constructor
declaration.
\begin{verbatim}

> checkDeclLabels :: ConstrDecl -> Error ()
> checkDeclLabels (ConstrDecl _ _ _ _ _) = return ()
> checkDeclLabels (ConOpDecl _ _ _ _ _ _) = return ()
> checkDeclLabels (RecordDecl p evs cx c fs) =
>   mapA_ (errorAt p . duplicateLabel "declaration" . fst)
>         (duplicates (labels (RecordDecl p evs cx c fs)))

\end{verbatim}
A goal is checked like the right hand side of a pattern declaration.
Thus, declarations in the goal's where clause are considered local
declarations. The final environment can be discarded.
\begin{verbatim}

> checkGoal :: VarEnv -> Goal a -> Error (Goal a)
> checkGoal env (Goal p e ds) =
>   do
>     (env',ds') <- checkLocalDecls env ds
>     e' <- checkExpr p env' e
>     return (Goal p e' ds')

> checkLocalDecls :: VarEnv -> [Decl a] -> Error (VarEnv,[Decl a])
> checkLocalDecls env ds =
>   do
>     env' <- checkDeclVars bindVar [] [] (nestEnv env) ds'
>     ds'' <- mapA (checkDecl env') ds'
>     return (env',ds'')
>   where ds' = joinEquations (map (disambDecl env) ds)

> disambDecl :: VarEnv -> Decl a -> Decl a
> disambDecl _ (InfixDecl p fix pr ops) = InfixDecl p fix pr ops
> disambDecl _ (TypeSig p vs ty) = TypeSig p vs ty
> disambDecl env (FunctionDecl p a _ [Equation p' lhs rhs]) =
>   case disambLhs env a lhs of
>     Left (a',f',lhs') -> FunctionDecl p a' f' [Equation p' lhs' rhs]
>     Right t' -> PatternDecl p' (disambTerm env t') rhs
> disambDecl _ (ForeignDecl p fi a f ty) = ForeignDecl p fi a f ty
> disambDecl env (PatternDecl p t rhs) = PatternDecl p (disambTerm env t) rhs
> disambDecl _ (FreeDecl p vs) = FreeDecl p vs
> disambDecl _ (TrustAnnot p t fs) = TrustAnnot p t fs

> disambLhs :: VarEnv -> a -> Lhs a -> Either (a,Ident,Lhs a) (ConstrTerm a)
> disambLhs env a (FunLhs f ts)
>   | isDataConstr env f = Right (ConstructorPattern a (qualify f) ts)
>   | otherwise = Left (a,f,FunLhs f ts)
> disambLhs env a (OpLhs t1 op t2)
>   | isDataConstr env op =
>       disambOpLhs env (infixPattern t1 (InfixConstr () (qualify op))) t2
>   | otherwise = Left (a,op,OpLhs t1 op t2)
>   where infixPattern (InfixPattern a t1 op1 t2) op2 t3 =
>           InfixPattern a t1 op1 (infixPattern t2 op2 t3)
>         infixPattern t1 op t2 = InfixPattern a t1 op t2
> disambLhs env a (ApLhs lhs ts) =
>   case disambLhs env a lhs of
>     Left (a',f',lhs') -> Left (a',f',ApLhs lhs' ts)
>     Right _ -> Left (a,f,ApLhs lhs ts)
>   where (f,_) = flatLhs lhs

> disambOpLhs :: VarEnv -> (ConstrTerm a -> ConstrTerm a) -> ConstrTerm a
>             -> Either (a,Ident,Lhs a) (ConstrTerm a)
> disambOpLhs env f (InfixPattern a t1 op t2)
>   | isJust m || isDataConstr env op' =
>       disambOpLhs env (f . InfixPattern a t1 op) t2
>   | otherwise = Left (a,op',OpLhs (f t1) op' t2)
>   where (m,op') = splitQualIdent (opName op)
> disambOpLhs _ f t = Right (f t)

> disambTerm :: VarEnv -> ConstrTerm a -> ConstrTerm a
> disambTerm _ (LiteralPattern a l) = LiteralPattern a l
> disambTerm _ (NegativePattern a l) = NegativePattern a l
> disambTerm env (VariablePattern a v)
>   | v == anonId = VariablePattern a v
>   | otherwise = disambTerm env (ConstructorPattern a (qualify v) [])
> disambTerm env (ConstructorPattern a c ts)
>   | any isConstr (qualLookupNestEnv c env) = ConstructorPattern a c ts'
>   | not (isQualified c) && null ts = VariablePattern a (unqualify c)
>   | otherwise = FunctionPattern a c ts'
>   where ts' = map (disambTerm env) ts
> disambTerm env (FunctionPattern a f ts) =
>   disambTerm env (ConstructorPattern a f ts)
> disambTerm env (InfixPattern a t1 op t2) =
>   InfixPattern a t1' (disambOp env (opName op)) t2'
>   where t1' = disambTerm env t1
>         t2' = disambTerm env t2
>         disambOp env op
>           | any isConstr (qualLookupNestEnv op env) = InfixConstr () op
>           | otherwise = InfixOp () op
> disambTerm env (ParenPattern t) = ParenPattern (disambTerm env t)
> disambTerm env (RecordPattern a c fs) =
>   RecordPattern a c [Field l (disambTerm env t) | Field l t <- fs]
> disambTerm env (TuplePattern ts) = TuplePattern (map (disambTerm env) ts)
> disambTerm env (ListPattern a ts) = ListPattern a (map (disambTerm env) ts)
> disambTerm env (AsPattern v t) = AsPattern v (disambTerm env t)
> disambTerm env (LazyPattern t) = LazyPattern (disambTerm env t)

> checkDeclVars :: (P Ident -> VarEnv -> VarEnv) -> [P Ident] -> [P Ident]
>               -> VarEnv -> [Decl a] -> Error VarEnv
> checkDeclVars bindVar xs fs env ds =
>   reportDuplicates duplicatePrecedence repeatedPrecedence ops *>
>   reportDuplicates duplicateDefinition repeatedDefinition
>                    (mergeBy comparePos xs (mergeBy comparePos fs bvs)) *>
>   reportDuplicates duplicateTypeSig repeatedTypeSig tys *>
>   reportDuplicates (const duplicateDefaultTrustAnnot)
>                    (const repeatedDefaultTrustAnnot)
>                    [P p () | TrustAnnot p _ [] <- ds] *>
>   reportDuplicates duplicateTrustAnnot repeatedTrustAnnot trs *>
>   mapA_ (\(P p v) -> errorAt p (noBody v))
>         (filter (`notElem` xs ++ fs ++ bvs) ops ++
>          filter (`notElem` bvs) (tys ++ trs)) *>
>   return (foldr bindVar env (fs ++ bvs))
>   where bvs = concatMap vars (filter isValueDecl ds)
>         tys = concatMap vars (filter isTypeSig ds)
>         trs = concatMap vars (filter isTrustAnnot ds)
>         ops = concatMap vars (filter isInfixDecl ds)

\end{verbatim}
\ToDo{The syntax checker should accept trust annotations only for
  defined functions because they have no effect on local variables and
  foreign functions.}
\begin{verbatim}

> checkDecl :: VarEnv -> Decl a -> Error (Decl a)
> checkDecl _ (InfixDecl p fix pr ops) = return (InfixDecl p fix pr ops)
> checkDecl _ (TypeSig p fs ty) = return (TypeSig p fs ty)
> checkDecl env (FunctionDecl p a f eqs) =
>   checkArity p f eqs *>
>   liftA (FunctionDecl p a f) (mapA (checkEquation env) eqs)
> checkDecl _ (ForeignDecl p fi a f ty) =
>   do
>     fi' <- checkForeign p f fi
>     return (ForeignDecl p fi' a f ty)
> checkDecl env (PatternDecl p t rhs) =
>   liftA2 (PatternDecl p) (checkConstrTerm p env t) (checkRhs env rhs)
> checkDecl _ (FreeDecl p vs) = return (FreeDecl p vs)
> checkDecl _ (TrustAnnot p tr fs) = return (TrustAnnot p tr fs)

> checkArity :: Position -> Ident -> [Equation a] -> Error ()
> checkArity p f eqs = unless (sameArity eqs) (errorAt p (differentArity f))
>   where sameArity = null . tail . nub . map eqnArity

> joinEquations :: [Decl a] -> [Decl a]
> joinEquations [] = []
> joinEquations (FunctionDecl p a f eqs : FunctionDecl p' _ f' [eq] : ds)
>   | f == f' = joinEquations (FunctionDecl p a f (eqs ++ [eq]) : ds)
> joinEquations (d : ds) = d : joinEquations ds

> checkEquation :: VarEnv -> Equation a -> Error (Equation a)
> checkEquation env (Equation p lhs rhs) =
>   do
>     (env',lhs') <- checkLhs p env lhs
>     rhs' <- checkRhs env' rhs
>     return (Equation p lhs' rhs')

\end{verbatim}
The method declarations in an instance declaration and also the
default method declarations in a class declaration are checked like
any other declaration group except that the declared methods are not
added to the variable name environment. Instead, the compiler checks
that the declared methods are members of the specified class. Note
that in an instance declaration the method names are required to be in
scope, but the name under which a method is in scope is immaterial
(cf.\ Sect.~4.3.2 of the revised Haskell'98
report~\cite{PeytonJones03:Haskell}).
\begin{verbatim}

> checkMethodDecls :: VarEnv -> QualIdent -> [P Ident] -> [P Ident] -> [Decl a]
>                  -> Error [Decl a]
> checkMethodDecls env cls ops fs ds =
>   do
>     ds' <- liftA joinEquations (mapA (disambBlockDecl env) ds)
>     checkMethods cls ops fs ds'
>     mapA (checkDecl env) ds'

> checkMethods :: QualIdent -> [P Ident] -> [P Ident] -> [Decl a] -> Error ()
> checkMethods cls ops fs ds =
>   reportDuplicates duplicatePrecedence repeatedPrecedence (ops ++ ops') *>
>   reportDuplicates duplicateDefinition repeatedDefinition fs' *>
>   reportDuplicates (const duplicateDefaultTrustAnnot)
>                    (const repeatedDefaultTrustAnnot)
>                    [P p () | TrustAnnot p _ [] <- ds] *>
>   reportDuplicates duplicateTrustAnnot repeatedTrustAnnot trs *>
>   mapA_ (\(P p f) -> errorAt p (undefinedMethod cls f))
>         (filter (`notElem` fs) (ops' ++ fs')) *>
>     mapA_ (\(P p f) -> errorAt p (noBody f)) (filter (`notElem` fs') trs)
>   where fs' = [P p f | FunctionDecl p _ f _ <- ds]
>         ops' = concatMap vars (filter isInfixDecl ds)
>         trs = concatMap vars (filter isTrustAnnot ds)

\end{verbatim}
The syntax checker examines the optional import specification of
foreign function declarations. For functions using the \texttt{ccall}
and \texttt{rawcall} calling conventions, the syntax from the Haskell
98 foreign function interface addendum~\cite{Chakravarty03:FFI} is
supported, except for \texttt{wrapper} specifications, which are not
recognized because callbacks into Curry are not yet supported by the
runtime system.
\begin{verbatim}

> checkForeign :: Position -> Ident -> ForeignImport -> Error ForeignImport
> checkForeign p f (cc,s,ie)
>   | cc == CallConvPrimitive = return (cc,s,ie)
>   | otherwise =
>       maybe (checkFunName f >> return (cc,s,Nothing))
>             (impEnt cc s . words . join . break ('&' ==))
>             ie
>   where join (cs,[]) = cs
>         join (cs,c':cs') = cs ++ [' ',c',' '] ++ cs'
>         impEnt cc s ie = kind ie >> return (cc,s,Just (unwords ie))
>         kind [] = ident []
>         kind (x:xs)
>           | x == "static" = header xs
>           | x == "dynamic" = end x xs
>           | otherwise = header (x:xs)
>         header [] = ident []
>         header (x:xs)
>           | not (".h" `isSuffixOf` x) = addr (x:xs)
>           | all isHeaderChar x = addr xs
>           | otherwise = errorAt p (invalidCImpEnt (notCHeader x) ie)
>         addr [] = ident []
>         addr (x:xs)
>           | x == "&" = ident xs
>           | otherwise = ident (x:xs)
>         ident [] = checkFunName f
>         ident (x:xs)
>           | isCIdent x = end ("C identifier " ++ x) xs
>           | otherwise = errorAt p (invalidCImpEnt (notCIdent x) ie)
>         end what xs
>           | null xs = return ()
>           | otherwise = errorAt p (invalidCImpEnt (junkAfter what) ie)
>         checkFunName f
>           | isCIdent f' = return ()
>           | otherwise = errorAt p (invalidCImpEnt (notCIdent f') Nothing)
>           where f' = name f
>         isCIdent [] = False
>         isCIdent (c:cs) = isLetter c && all isLetNum cs
>         isLetter c = isAlpha c || c == '_'
>         isLetNum c = isLetter c || isDigit c
>         isHeaderChar c = isLetNum c || c `elem` "!#$%*+./<=>?@\\^|-~"

> checkLhs :: Position -> VarEnv -> Lhs a -> Error (VarEnv,Lhs a)
> checkLhs p env lhs =
>   do
>     lhs' <- checkLhsTerm p env lhs
>     env' <- checkBoundVars p env lhs'
>     return (env',lhs')

> checkLhsTerm :: Position -> VarEnv -> Lhs a -> Error (Lhs a)
> checkLhsTerm p env (FunLhs f ts) =
>   liftA (FunLhs f) (mapA (checkConstrTerm p env) ts)
> checkLhsTerm p env (OpLhs t1 op t2) =
>   liftA2 (flip OpLhs op) (checkConstrTerm p env t1) (checkConstrTerm p env t2)
> checkLhsTerm p env (ApLhs lhs ts) =
>   liftA2 ApLhs (checkLhsTerm p env lhs) (mapA (checkConstrTerm p env) ts)

> checkArg :: Position -> VarEnv -> ConstrTerm a -> Error (VarEnv,ConstrTerm a)
> checkArg p env t =
>   do
>     t' <- checkConstrTerm p env t
>     env' <- checkBoundVars p env t'
>     return (env',t')

> checkArgs :: Position -> VarEnv -> [ConstrTerm a]
>           -> Error (VarEnv,[ConstrTerm a])
> checkArgs p env ts =
>   do
>     ts' <- mapA (checkConstrTerm p env) ts
>     env' <- checkBoundVars p env ts'
>     return (env',ts')

> checkBoundVars :: QuantExpr t => Position -> VarEnv -> t -> Error VarEnv
> checkBoundVars p env ts =
>   do
>     mapA_ (errorAt p . duplicateVariable . fst) (duplicates bvs)
>     return (foldr (bindVar . P p) (nestEnv env) bvs)
>   where bvs = bv ts

> checkConstrTerm :: Position -> VarEnv -> ConstrTerm a -> Error (ConstrTerm a)
> checkConstrTerm _ _ (LiteralPattern a l) = return (LiteralPattern a l)
> checkConstrTerm _ _ (NegativePattern a l) = return (NegativePattern a l)
> checkConstrTerm p env (VariablePattern a v)
>   | v == anonId = return (VariablePattern a v)
>   | otherwise = checkConstrTerm p env (ConstructorPattern a (qualify v) [])
> checkConstrTerm p env (ConstructorPattern a c ts)
>   | not (isQualified c) && null ts =
>       case qualLookupNestEnv c env of
>         [Constr _] -> return (ConstructorPattern a c [])
>         rs
>           | any isConstr rs -> errorAt p (ambiguousData rs c)
>           | otherwise -> return (VariablePattern a (unqualify c))
>   | otherwise =
>       liftA2 ($)
>              (case qualLookupNestEnv c env of
>                 [] -> errorAt p (undefinedData c)
>                 [Constr _] -> return (ConstructorPattern a c)
>                 [Var _ _] -> return (FunctionPattern a c)
>                 rs
>                   | any isConstr rs -> errorAt p (ambiguousData rs c)
>                   | otherwise -> errorAt p (ambiguousFunction rs c))
>              (mapA (checkConstrTerm p env) ts)
> checkConstrTerm p env (FunctionPattern a f ts) =
>   checkConstrTerm p env (ConstructorPattern a f ts)
> checkConstrTerm p env (InfixPattern a t1 op t2) =
>   liftA3 (InfixPattern a)
>          (checkConstrTerm p env t1)
>          (case qualLookupNestEnv op' env of
>             [] -> errorAt p (undefinedData op')
>             [Constr _] -> return (InfixConstr () op')
>             [Var _ _] -> return (InfixOp () op')
>             rs
>               | any isConstr rs -> errorAt p (ambiguousData rs op')
>               | otherwise -> errorAt p (ambiguousFunction rs op'))
>          (checkConstrTerm p env t2)
>   where op' = opName op
> checkConstrTerm p env (ParenPattern t) =
>   liftA ParenPattern (checkConstrTerm p env t)
> checkConstrTerm p env (RecordPattern a c fs) =
>   do
>     fs' <-
>       (case qualLookupNestEnv c env of
>          [Constr _] -> return ()
>          rs
>            | any isConstr rs -> errorAt p (ambiguousData rs c)
>            | otherwise -> errorAt p (undefinedData c)) *>
>       mapA (checkField (checkConstrTerm p env)) fs
>     checkFieldLabels "pattern" p env (Just c) fs'
>     return (RecordPattern a c fs')
> checkConstrTerm p env (TuplePattern ts) =
>   liftA TuplePattern (mapA (checkConstrTerm p env) ts)
> checkConstrTerm p env (ListPattern a ts) =
>   liftA (ListPattern a) (mapA (checkConstrTerm p env) ts)
> checkConstrTerm p env (AsPattern v t) =
>   liftA (AsPattern v) (checkConstrTerm p env t)
> checkConstrTerm p env (LazyPattern t) =
>   liftA LazyPattern (checkConstrTerm p env t)

> checkRhs :: VarEnv -> Rhs a -> Error (Rhs a)
> checkRhs env (SimpleRhs p e ds) =
>   do
>     (env',ds') <- checkLocalDecls env ds
>     e' <- checkExpr p env' e
>     return (SimpleRhs p e' ds')
> checkRhs env (GuardedRhs es ds) =
>   do
>     (env',ds') <- checkLocalDecls env ds
>     es' <- mapA (checkCondExpr env') es
>     return (GuardedRhs es' ds')

> checkCondExpr :: VarEnv -> CondExpr a -> Error (CondExpr a)
> checkCondExpr env (CondExpr p g e) =
>   liftA2 (CondExpr p) (checkExpr p env g) (checkExpr p env e)

> checkExpr :: Position -> VarEnv -> Expression a -> Error (Expression a)
> checkExpr _ _ (Literal a l) = return (Literal a l)
> checkExpr p env (Variable a v)
>   | unqualify v == anonId = return (Variable a v)
>   | otherwise =
>       case qualLookupNestEnv v env of
>         [] -> errorAt p (undefinedVariable v)
>         [Constr _] -> return (Constructor a v)
>         [Var _ _] -> return (Variable a v)
>         rs -> errorAt p (ambiguousIdent rs v)
> checkExpr p env (Constructor a c) = checkExpr p env (Variable a c)
> checkExpr p env (Paren e) = liftA Paren (checkExpr p env e)
> checkExpr p env (Typed e ty) = liftA (flip Typed ty) (checkExpr p env e)
> checkExpr p env (Record a c fs)
>   | null fs =
>       case qualLookupNestEnv c env of
>         [Constr _] -> return (Record a c [])
>         rs
>           | any isConstr rs -> errorAt p (ambiguousData rs c)
>           | otherwise -> errorAt p (undefinedData c)
>   | otherwise = checkExpr p env (RecordUpdate (Constructor a c) fs)
> checkExpr p env (RecordUpdate e fs) =
>   do
>     (e',fs') <-
>       liftA (,) (checkExpr p env e) <*> mapA (checkField (checkExpr p env)) fs
>     case e' of
>       Constructor a c ->
>         do
>           checkFieldLabels "construction" p env (Just c) fs'
>           return (Record a c fs')
>       _ ->
>         do
>           checkFieldLabels "update" p env Nothing fs'
>           return (RecordUpdate e' fs')
> checkExpr p env (Tuple es) = liftA Tuple (mapA (checkExpr p env) es)
> checkExpr p env (List a es) = liftA (List a) (mapA (checkExpr p env) es)
> checkExpr p env (ListCompr e qs) =
>   do
>     (env',qs') <- mapAccumM (checkStmt p) env qs
>     e' <- checkExpr p env' e
>     return (ListCompr e' qs')
> checkExpr p env (EnumFrom e) = liftA EnumFrom (checkExpr p env e)
> checkExpr p env (EnumFromThen e1 e2) =
>   liftA2 EnumFromThen (checkExpr p env e1) (checkExpr p env e2)
> checkExpr p env (EnumFromTo e1 e2) =
>   liftA2 EnumFromTo (checkExpr p env e1) (checkExpr p env e2)
> checkExpr p env (EnumFromThenTo e1 e2 e3) =
>   liftA3 EnumFromThenTo
>          (checkExpr p env e1)
>          (checkExpr p env e2)
>          (checkExpr p env e3)
> checkExpr p env (UnaryMinus e) = liftA UnaryMinus (checkExpr p env e)
> checkExpr p env (Apply e1 e2) =
>   liftA2 Apply (checkExpr p env e1) (checkExpr p env e2)
> checkExpr p env (InfixApply e1 op e2) =
>   liftA3 InfixApply
>          (checkExpr p env e1)
>          (checkOp p env op)
>          (checkExpr p env e2)
> checkExpr p env (LeftSection e op) =
>   liftA2 LeftSection (checkExpr p env e) (checkOp p env op)
> checkExpr p env (RightSection op e) =
>   liftA2 RightSection (checkOp p env op) (checkExpr p env e)
> checkExpr _ env (Lambda p ts e) =
>   do
>     (env',ts') <- checkArgs p env ts
>     e' <- checkExpr p env' e
>     return (Lambda p ts' e')
> checkExpr p env (Let ds e) =
>   do
>     (env',ds') <- checkLocalDecls env ds
>     e' <- checkExpr p env' e
>     return (Let ds' e')
> checkExpr p env (Do sts e) =
>   do
>     (env',sts') <- mapAccumM (checkStmt p) env sts
>     e' <- checkExpr p env' e
>     return (Do sts' e')
> checkExpr p env (IfThenElse e1 e2 e3) =
>   liftA3 IfThenElse
>          (checkExpr p env e1)
>          (checkExpr p env e2)
>          (checkExpr p env e3)
> checkExpr p env (Case e alts) =
>   liftA2 Case (checkExpr p env e) (mapA (checkAlt env) alts)
> checkExpr p env (Fcase e alts) =
>   liftA2 Fcase (checkExpr p env e) (mapA (checkAlt env) alts)

> checkStmt :: Position -> VarEnv -> Statement a -> Error (VarEnv,Statement a)
> checkStmt p env (StmtExpr e) =
>   do
>     e' <- checkExpr p env e
>     return (env,StmtExpr e')
> checkStmt _ env (StmtBind p t e) =
>   do
>     e' <- checkExpr p env e
>     (env',t') <- checkArg p env t
>     return (env',StmtBind p t' e')
> checkStmt _ env (StmtDecl ds) =
>   do
>     (env',ds') <- checkLocalDecls env ds
>     return (env',StmtDecl ds')

> checkAlt :: VarEnv -> Alt a -> Error (Alt a)
> checkAlt env (Alt p t rhs) =
>   do
>     (env',t') <- checkArg p env t
>     rhs' <- checkRhs env' rhs
>     return (Alt p t' rhs')

> checkOp :: Position -> VarEnv -> InfixOp a -> Error (InfixOp a)
> checkOp p env op =
>   case qualLookupNestEnv v env of
>     [] -> errorAt p (undefinedVariable v)
>     [Constr _] -> return (InfixConstr (attr op) v)
>     [Var _ _] -> return (InfixOp (attr op) v)
>     rs -> errorAt p (ambiguousIdent rs v)
>   where v = opName op
>         attr (InfixOp a _) = a
>         attr (InfixConstr a _) = a

\end{verbatim}
For record patterns and expressions the compiler checks that all field
labels belong to the pattern or expression's constructor. For record
update expressions, the compiler checks that there is at least one
constructor which has all the specified field labels. In addition, the
compiler always checks that no field label occurs twice. Field labels
are always looked up in the global environment since they cannot be
shadowed by local variables (cf.\ Sect.~3.15.1 of the revised
Haskell'98 report~\cite{PeytonJones03:Haskell}).
\begin{verbatim}

> checkFieldLabels :: String -> Position -> VarEnv -> Maybe QualIdent
>                  -> [Field a] -> Error ()
> checkFieldLabels what p env c fs =
>   do
>     mapA (checkFieldLabel p env) ls' >>= checkLabels p env c ls'
>     mapA_ (errorAt p . duplicateLabel what . fst)
>           (duplicates (map unqualify ls))
>   where ls = [l | Field l _ <- fs]
>         ls' = nub ls

> checkFieldLabel :: Position -> VarEnv -> QualIdent -> Error [QualIdent]
> checkFieldLabel p env l =
>   case qualLookupNestEnv l (globalEnv (toplevelEnv env)) of
>     [Var _ cs]
>       | null cs -> errorAt p (undefinedLabel l)
>       | otherwise -> return cs
>     rs
>       | any isLabel rs -> errorAt p (ambiguousLabel rs l)
>       | otherwise -> errorAt p (undefinedLabel l)

> checkLabels :: Position -> VarEnv -> Maybe QualIdent -> [QualIdent]
>             -> [[QualIdent]] -> Error ()
> checkLabels p env (Just c) ls css =
>   mapA_ (errorAt p . noLabel c) [l | (l,cs) <- zip ls css, c' `notElem` cs]
>   where c' = origName (head (qualLookupNestEnv c env))
> checkLabels p _ Nothing ls css =
>   when (null (foldr1 intersect css)) (errorAt p (noCommonConstr ls))

> checkField :: (a -> Error a) -> Field a -> Error (Field a)
> checkField check (Field l x) = liftA (Field l) (check x)

\end{verbatim}
Auxiliary definitions.
\begin{verbatim}

> constrs :: TopDecl a -> [P Ident]
> constrs (DataDecl _ _ _ _ cs _) = map constr cs
>   where constr (ConstrDecl p _ _ c _) = P p c
>         constr (ConOpDecl p _ _ _ op _) = P p op
>         constr (RecordDecl p _ _ c _) = P p c
> constrs (NewtypeDecl _ _ _ _ nc _) = [nconstr nc]
>   where nconstr (NewConstrDecl p c _) = P p c
>         nconstr (NewRecordDecl p c _ _) = P p c
> constrs (TypeDecl _ _ _ _) = []
> constrs (ClassDecl _ _ _ _ _) = []
> constrs (InstanceDecl _ _ _ _ _) = []
> constrs (DefaultDecl _ _) = []
> constrs (BlockDecl _) = []

> fieldLabels :: TopDecl a -> [(P Ident,[Ident])]
> fieldLabels (DataDecl _ _ _ _ cs _) =
>   [(l,constrs cs l) | l <- nub (concatMap labels cs)]
>   where constrs cs l = [constr c | c <- cs, l `elem` labels c]
>         labels (ConstrDecl _ _ _ _ _) = []
>         labels (ConOpDecl _ _ _ _ _ _) = []
>         labels (RecordDecl _ _ _ _ fs) =
>           [P p l | FieldDecl p ls _ <- fs, l <- ls]
> fieldLabels (NewtypeDecl _ _ _ _ nc _) = nlabel nc
>   where nlabel (NewConstrDecl _ _ _) = []
>         nlabel (NewRecordDecl p c l _) = [(P p l,[c])]
> fieldLabels (TypeDecl _ _ _ _) = []
> fieldLabels (ClassDecl _ _ _ _ _) = []
> fieldLabels (InstanceDecl _ _ _ _ _) = []
> fieldLabels (DefaultDecl _ _) = []
> fieldLabels (BlockDecl _) = []

> mthds :: TopDecl a -> [P Ident]
> mthds (DataDecl _ _ _ _ _ _) = []
> mthds (NewtypeDecl _ _ _ _ _ _) = []
> mthds (TypeDecl _ _ _ _) = []
> mthds (ClassDecl _ _ _ _ ds) = [P p f | TypeSig p fs _ <- ds, f <- fs]
> mthds (InstanceDecl _ _ _ _ _) = []
> mthds (DefaultDecl _ _) = []
> mthds (BlockDecl _) = []

> vars :: Decl a -> [P Ident]
> vars (InfixDecl p _ _ ops) = map (P p) ops
> vars (TypeSig p fs _) = map (P p) fs
> vars (FunctionDecl p _ f _) = [P p f]
> vars (ForeignDecl p _ _ f _) = [P p f]
> vars (PatternDecl p t _) = map (P p) (bv t)
> vars (FreeDecl p vs) = map (P p) (bv vs)
> vars (TrustAnnot p _ fs) = map (P p) fs

\end{verbatim}
Due to the lack of a capitalization convention in Curry, it is
possible that an identifier may ambiguously refer to a data
constructor and a function provided that both are imported from some
other module. For the purpose of disambiguating the left hand sides of
operator declarations, we consider an identifier to denote a data
constructor only if it does so unambiguously.
\begin{verbatim}

> isDataConstr :: VarEnv -> Ident -> Bool
> isDataConstr env v =
>   case lookupNestEnv v env of
>     [Constr _] -> True
>     _ -> False

> isConstr :: ValueKind -> Bool
> isConstr (Constr _) = True
> isConstr (Var _ _) = False

> isLabel :: ValueKind -> Bool
> isLabel (Constr _) = False
> isLabel (Var _ cs) = not (null cs)

> classMthds :: QualIdent -> TypeEnv -> [Ident]
> classMthds cls tEnv =
>   case qualLookupTopEnv cls tEnv of
>     [Class _ fs] -> fs
>     _ -> internalError "classMthds"

\end{verbatim}
Auxiliary functions.
\begin{verbatim}

> comparePos :: P a -> P a -> Ordering
> comparePos (P p1 _) (P p2 _) = compare p1 p2

\end{verbatim}
The functions \texttt{merge} and \texttt{mergeBy} merge two already
sorted lists.

\ToDo{The function \texttt{merge} is commented out because it
  conflicts with a method of the \texttt{Entity} class and thus
  prevents compilation with hbc.}
\begin{verbatim}

merge :: Ord a => [a] -> [a] -> [a]
merge = mergeBy compare

> mergeBy :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
> mergeBy _ [] ys = ys
> mergeBy _ (x:xs) [] = x:xs
> mergeBy cmp (x:xs) (y:ys) =
>   case cmp x y of
>     GT -> y : mergeBy cmp (x:xs) ys
>     _ -> x : mergeBy cmp xs (y:ys)

\end{verbatim}
Error messages.
\begin{verbatim}

> reportDuplicates :: Eq a => (a -> String) -> (a -> String) -> [P a]
>                  -> Error ()
> reportDuplicates f1 f2 xs =
>   mapA_ (\(x,xs) -> zipWithA_ report (f1 : repeat f2) (x:xs)) (duplicates xs)
>   where report f (P p x) = errorAt p (f x)

> undefinedVariable :: QualIdent -> String
> undefinedVariable v = qualName v ++ " is undefined"

> undefinedData :: QualIdent -> String
> undefinedData c = "Undefined data constructor " ++ qualName c

> undefinedLabel :: QualIdent -> String
> undefinedLabel l = "Undefined field label " ++ qualName l

> undefinedMethod :: QualIdent -> Ident -> String
> undefinedMethod cls f = name f ++ " is not a method of class " ++ qualName cls

> ambiguousIdent :: [ValueKind] -> QualIdent -> String
> ambiguousIdent rs
>   | any isConstr rs = ambiguousData rs
>   | otherwise = ambiguousVariable rs

> ambiguousVariable :: [ValueKind] -> QualIdent -> String
> ambiguousVariable = ambiguous "variable"

> ambiguousFunction :: [ValueKind] -> QualIdent -> String
> ambiguousFunction = ambiguous "function"

> ambiguousData :: [ValueKind] -> QualIdent -> String
> ambiguousData = ambiguous "data constructor"

> ambiguousLabel :: [ValueKind] -> QualIdent -> String
> ambiguousLabel = ambiguous "field label"

> ambiguous :: String -> [ValueKind] -> QualIdent -> String
> ambiguous what rs x = show $
>   text "Ambiguous" <+> text what <+> ppQIdent x $$
>   fsep (text "Could refer to:" :
>         punctuate comma (map (ppQIdent . origName) rs))

> duplicateDefinition :: Ident -> String
> duplicateDefinition v = name v ++ " defined more than once"

> repeatedDefinition :: Ident -> String
> repeatedDefinition v = "Redefinition of " ++ name v

> duplicateLabel :: String -> Ident -> String
> duplicateLabel what l =
>   "Field label " ++ name l ++ " occurs more than once in record " ++ what

> duplicateVariable :: Ident -> String
> duplicateVariable v = name v ++ " occurs more than once in pattern"

> duplicateData :: Ident -> String
> duplicateData c = "Data constructor " ++ name c ++ " defined more than once"

> repeatedData :: Ident -> String
> repeatedData c = "Redefinition of constructor " ++ name c

> duplicatePrecedence :: Ident -> String
> duplicatePrecedence op = "More than one fixity declaration for " ++ name op

> repeatedPrecedence :: Ident -> String
> repeatedPrecedence op = "Repeated fixity declaration for " ++ name op

> duplicateTypeSig :: Ident -> String
> duplicateTypeSig v = "More than one type signature for " ++ name v

> repeatedTypeSig :: Ident -> String
> repeatedTypeSig v = "Repeated type signature for " ++ name v

> duplicateDefaultTrustAnnot :: String
> duplicateDefaultTrustAnnot =
>   "More than one default trust annotation in this scope"

> repeatedDefaultTrustAnnot :: String
> repeatedDefaultTrustAnnot = "Repeated default trust annotation"

> duplicateTrustAnnot :: Ident -> String
> duplicateTrustAnnot f = "More than one trust annotation for " ++ name f

> repeatedTrustAnnot :: Ident -> String
> repeatedTrustAnnot f = "Repeated trust annotation for " ++ name f

> noLabel :: QualIdent -> QualIdent -> String
> noLabel c l =
>   qualName l ++ " is not a field label of constructor " ++ show c

> noCommonConstr :: [QualIdent] -> String
> noCommonConstr ls =
>   "No constructor has all of these fields: " ++
>   concat (intersperse ", " (map qualName ls))

> noBody :: Ident -> String
> noBody v = name v ++ " is not defined in this scope"

> noToplevelPattern :: String
> noToplevelPattern = "Pattern declaration not allowed at top-level"

> differentArity :: Ident -> String
> differentArity f = "Varying number of arguments to function " ++ name f

> noExpressionStatement :: String
> noExpressionStatement =
>   "Last statement in a do expression must be an expression"

> invalidCImpEnt :: String -> Maybe String -> String
> invalidCImpEnt why Nothing =
>   unlines ["Error in ccall import declaration ",why]
> invalidCImpEnt why (Just ie) =
>   unlines ["Error in ccall import entity specification " ++ show ie,why]

> notCHeader :: String -> String
> notCHeader h = h ++ " is not a valid C header file name"

> notCIdent :: String -> String
> notCIdent f = f ++ " is not a valid C identifier"

> junkAfter :: String -> String
> junkAfter what = "Garbage after " ++ what

\end{verbatim}
