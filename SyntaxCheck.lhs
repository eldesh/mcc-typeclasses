% -*- LaTeX -*-
% $Id: SyntaxCheck.lhs 2046 2006-12-15 13:29:51Z wlux $
%
% Copyright (c) 1999-2006, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{SyntaxCheck.lhs}
\section{Syntax Checks}
After the type declarations have been checked, the compiler performs a
syntax check on the remaining declarations. This check disambiguates
nullary data constructors and variables, which cannot be done in the
parser because Curry -- in contrast to many other declarative
languages -- lacks a capitalization convention. In addition, this pass
checks for undefined as well as ambiguous variables and constructors.
Finally, all (adjacent) equations of a function are merged into a
single definition.
\begin{verbatim}

> module SyntaxCheck(syntaxCheck,syntaxCheckGoal) where
> import Base
> import Char
> import CurryPP
> import Error
> import List
> import Maybe
> import TopEnv
> import NestEnv
> import Pretty
> import Utils

\end{verbatim}
Syntax checking proceeds as follows. First, the compiler extracts
information about all imported values and data constructors from the
imported (type) environments. Next, the data constructors defined in
the current module are entered into this environment. Finally, all
declarations are checked within the resulting environment.
\begin{verbatim}

> syntaxCheck :: ModuleIdent -> TypeEnv -> ValueEnv -> [TopDecl a]
>             -> Error (FunEnv,[TopDecl a])
> syntaxCheck m tEnv tyEnv ds =
>   do
>     reportDuplicates duplicateData repeatedData cs
>     (env',ds') <- checkTopDecls m tEnv cs env ds
>     return (toplevelEnv env',ds')
>   where env = foldr (bindConstr m) (globalEnv (fmap valueKind tyEnv)) cs
>         cs = concatMap constrs ds

> syntaxCheckGoal :: ValueEnv -> Goal a -> Error (Goal a)
> syntaxCheckGoal tyEnv g = checkGoal (globalEnv (fmap valueKind tyEnv)) g

> bindConstr :: ModuleIdent -> P Ident -> VarEnv -> VarEnv
> bindConstr m (P _ c) = globalBindNestEnv m c (Constr (qualifyWith m c))

> bindFunc :: ModuleIdent -> P Ident -> VarEnv -> VarEnv
> bindFunc m (P _ f) = globalBindNestEnv m f (Var (qualifyWith m f))

> bindVar :: P Ident -> VarEnv -> VarEnv
> bindVar (P _ v) = localBindNestEnv v (Var (qualify v))

\end{verbatim}
When a module's global declaration group is checked, the compiler must
preserve the order of type and value declarations. This is necessary
in order to detect the error in the following code fragment.
\begin{verbatim}
  f = 0
  data T = C
  f = 1
\end{verbatim}
This error would go by unnoticed if the compiler would partition
top-level declarations into type and value declarations.
Unfortunately, this means that we cannot use \texttt{checkLocalDecls}
in order to check the global declaration group.

Note that fixity declarations for class methods can occur either at
the top-level of a module or in the class declaration itself
(cf.\ Sect.~4.4.2 of the revised Haskell'98
report~\cite{PeytonJones03:Haskell}). In order to detect duplicate
fixity declarations for class methods, the relevant top-level fixity
declarations are passed to \texttt{checkMethodDecls}.
\begin{verbatim}

> checkTopDecls :: ModuleIdent -> TypeEnv -> [P Ident] -> VarEnv -> [TopDecl a]
>               -> Error (VarEnv,[TopDecl a])
> checkTopDecls m tEnv cs env ds =
>   do
>     ds' <- liftE joinTopEquations (mapE (checkTopDeclLhs env) ds)
>     env' <- checkDeclVars (bindFunc m) cs (concatMap mthds ds') env
>                           [d | BlockDecl d <- ds']
>     ds'' <- mapE (checkTopDeclRhs tEnv env' ops) ds'
>     return (env',ds'')
>   where ops = [P p op | BlockDecl (InfixDecl p _ _ ops) <- ds, op <- ops]

> checkTopDeclLhs :: VarEnv -> TopDecl a -> Error (TopDecl a)
> checkTopDeclLhs env (ClassDecl p cx cls tv ds) =
>   do
>     mapE_ (checkMethodSig env) ds
>     return (ClassDecl p cx cls tv ds)
> checkTopDeclLhs env (BlockDecl d) = liftE BlockDecl (checkDeclLhs True env d)
> checkTopDeclLhs _ d = return d

> joinTopEquations :: [TopDecl a] -> [TopDecl a]
> joinTopEquations [] = []
> joinTopEquations (d : ds)
>   | isBlockDecl d =
>       map BlockDecl (joinEquations [d | BlockDecl d <- d:ds']) ++
>       joinTopEquations ds''
>   | otherwise = d : joinTopEquations ds
>   where (ds',ds'') = span isBlockDecl ds

> checkTopDeclRhs :: TypeEnv -> VarEnv -> [P Ident] -> TopDecl a
>                 -> Error (TopDecl a)
> checkTopDeclRhs _ env ops (ClassDecl p cx cls tv ds) =
>   liftE (ClassDecl p cx cls tv)
>         (checkMethodDecls env (qualify cls) (filter (`elem` fs) ops) fs ds)
>   where fs = mthds (ClassDecl p cx cls tv ds)
> checkTopDeclRhs tEnv env _ (InstanceDecl p cx cls ty ds) =
>   liftE (InstanceDecl p cx cls ty) (checkMethodDecls env cls [] fs ds)
>   where fs = map (P p) (classMthds cls tEnv)
> checkTopDeclRhs _ env _ (BlockDecl d) = liftE BlockDecl (checkDeclRhs env d)
> checkTopDeclRhs _ _ _ d = return d

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

\end{verbatim}
In each declaration group, first the left hand sides of all
declarations are checked and adjacent equations for the same function
are merged into a single definition. Next, the compiler checks that
there is a corresponding value definition for every fixity
declaration, type signature, and trust annotation in this group and
that there are no duplicate definitions. Finally, the right hand sides
are checked.

The function \texttt{checkDeclLhs} also handles the case where a
pattern declaration is recognized as a function declaration by the
parser. This happens, e.g., for the declaration \verb|Just x = y|
because the parser cannot distinguish nullary constructors and
functions. Note that pattern declarations are not allowed on the
top-level.
\begin{verbatim}

> checkLocalDecls :: VarEnv -> [Decl a] -> Error (VarEnv,[Decl a])
> checkLocalDecls env ds =
>   do
>     ds' <- liftE joinEquations (mapE (checkDeclLhs False env') ds)
>     env'' <- checkDeclVars bindVar [] [] env' ds'
>     ds'' <- mapE (checkDeclRhs env'') ds'
>     return (env'',ds'')
>   where env' = nestEnv env

> checkMethodSig :: VarEnv -> MethodDecl a -> Error ()
> checkMethodSig _ (MethodFixity _ _ _ _) = return ()
> checkMethodSig env (MethodSig p fs _) = checkVars "type signature" p env fs
> checkMethodSig _ (MethodDecl _ _ _) = return ()

> checkDeclLhs :: Bool -> VarEnv -> Decl a -> Error (Decl a)
> checkDeclLhs _ _ (InfixDecl p fix pr ops) = return (InfixDecl p fix pr ops)
> checkDeclLhs _ env (TypeSig p vs ty) =
>   do
>     checkVars "type signature" p env vs
>     return (TypeSig p vs ty)
> checkDeclLhs top env (FunctionDecl p _ eqs) = checkEquationLhs top env p eqs
> checkDeclLhs _ env (ForeignDecl p cc ie f ty) =
>   do
>     checkVars "foreign declaration" p env [f]
>     return (ForeignDecl p cc ie f ty)
> checkDeclLhs top env (PatternDecl p t rhs)
>   | top = internalError "checkDeclLhs"
>   | otherwise = liftE (flip (PatternDecl p) rhs) (checkConstrTerm p env t)
> checkDeclLhs top env (FreeDecl p vs)
>   | top = internalError "checkDeclLhs"
>   | otherwise =
>       do
>         checkVars "free variables declaration" p env vs
>         return (FreeDecl p vs)
> checkDeclLhs top env (TrustAnnot p t fs) =
>   do
>     maybe (return ()) (checkVars "trust annotation" p env) fs
>     return (TrustAnnot p t fs)

> checkEquationLhs :: Bool -> VarEnv -> Position -> [Equation a]
>                  -> Error (Decl a)
> checkEquationLhs top env p [Equation p' lhs rhs] =
>   either funDecl patDecl (checkEqLhs env p' lhs)
>   where funDecl (f,lhs)
>           | isDataConstr env f =
>               errorAt p (nonVariable "curried definition" f)
>           | otherwise = return (FunctionDecl p f [Equation p' lhs rhs])
>         patDecl t
>           | top = errorAt p noToplevelPattern
>           | otherwise = checkDeclLhs top env (PatternDecl p' t rhs)
> checkEquationLhs _ _ _ _ = internalError "checkEquationLhs"

> checkEqLhs :: VarEnv -> Position -> Lhs a
>            -> Either (Ident,Lhs a) (ConstrTerm a)
> checkEqLhs env _ (FunLhs f ts)
>   | isDataConstr env f =
>       -- FIXME: need a better attribute value here
>       Right (ConstructorPattern undefined (qualify f) ts)
>   | otherwise = Left (f,FunLhs f ts)
> checkEqLhs env _ (OpLhs t1 op t2)
>   | isDataConstr env op = checkOpLhs env (infixPattern t1 (qualify op)) t2
>   | otherwise = Left (op,OpLhs t1 op t2)
>   where infixPattern (InfixPattern a t1 op1 t2) op2 t3 =
>           InfixPattern a t1 op1 (infixPattern t2 op2 t3)
>         infixPattern t1 op t2 = InfixPattern undefined t1 op t2
>           -- FIXME: need a better attribute value here
> checkEqLhs env p (ApLhs lhs ts) =
>   case checkEqLhs env p lhs of
>     Left (f',lhs') -> Left (f',ApLhs lhs' ts)
>     Right _ -> Left (f,ApLhs lhs ts)
>   where (f,_) = flatLhs lhs

> checkOpLhs :: VarEnv -> (ConstrTerm a -> ConstrTerm a) -> ConstrTerm a
>            -> Either (Ident,Lhs a) (ConstrTerm a)
> checkOpLhs env f (InfixPattern a t1 op t2)
>   | isJust m || isDataConstr env op' =
>       checkOpLhs env (f . InfixPattern a t1 op) t2
>   | otherwise = Left (op',OpLhs (f t1) op' t2)
>   where (m,op') = splitQualIdent op
> checkOpLhs _ f t = Right (f t)

> checkVars :: String -> Position -> VarEnv -> [Ident] -> Error ()
> checkVars what p env vs =
>   mapE_ (errorAt p . nonVariable what) (nub (filter (isDataConstr env) vs))

> checkDeclVars :: (P Ident -> VarEnv -> VarEnv) -> [P Ident] -> [P Ident]
>               -> VarEnv -> [Decl a] -> Error VarEnv
> checkDeclVars bindVar cs fs env ds =
>   reportDuplicates duplicatePrecedence repeatedPrecedence ops &&>
>   reportDuplicates duplicateDefinition repeatedDefinition (fs ++ bvs) &&>
>   reportDuplicates duplicateTypeSig repeatedTypeSig tys &&>
>   reportDuplicates (const duplicateDefaultTrustAnnot)
>                    (const repeatedDefaultTrustAnnot)
>                    [P p () | TrustAnnot p _ Nothing <- ds] &&>
>   reportDuplicates duplicateTrustAnnot repeatedTrustAnnot trs &&>
>   mapE_ (\(P p v) -> errorAt p (noBody v))
>         (filter (`notElem` cs ++ fs ++ bvs) ops ++
>          filter (`notElem` bvs) (tys ++ trs)) &&>
>   return (foldr bindVar env (nub (fs ++ bvs)))
>   where bvs = concatMap vars (filter isValueDecl ds)
>         tys = concatMap vars (filter isTypeSig ds)
>         trs = concatMap vars (filter isTrustAnnot ds)
>         ops = concatMap vars (filter isInfixDecl ds)

\end{verbatim}
\ToDo{The syntax checker should accept trust annotations only for
  defined functions because they have no effect on local variables and
  foreign functions.}
\begin{verbatim}

> checkDeclRhs :: VarEnv -> Decl a -> Error (Decl a)
> checkDeclRhs env (FunctionDecl p f eqs) =
>   checkArity p f eqs &&>
>   liftE (FunctionDecl p f) (mapE (checkEquation env) eqs)
> checkDeclRhs env (PatternDecl p t rhs) =
>   liftE (PatternDecl p t) (checkRhs env rhs)
> checkDeclRhs _ (ForeignDecl p cc ie f ty) =
>   do
>     ie' <- checkForeign p f cc ie
>     return (ForeignDecl p cc ie' f ty)
> checkDeclRhs _ d = return d

> checkArity :: Position -> Ident -> [Equation a] -> Error ()
> checkArity p f eqs
>   | null (tail (nub (map arity eqs))) = return ()
>   | otherwise = errorAt p (differentArity f)
>   where arity (Equation _ lhs _) = length (snd (flatLhs lhs))

> joinEquations :: [Decl a] -> [Decl a]
> joinEquations [] = []
> joinEquations (FunctionDecl p f eqs : FunctionDecl p' f' [eq] : ds)
>   | f == f' = joinEquations (FunctionDecl p f (eqs ++ [eq]) : ds)
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

> checkMethodDecls :: VarEnv -> QualIdent -> [P Ident] -> [P Ident]
>                  -> [MethodDecl a] -> Error [MethodDecl a]
> checkMethodDecls env cls ops fs ds =
>   do
>     ds' <- liftE joinEquations (mapE (checkMethodDeclLhs env) ds)
>     checkMethods cls ops fs ds'
>     mapE (checkMethodDeclRhs env) ds'

> checkMethodDeclLhs :: VarEnv -> MethodDecl a -> Error (Decl a)
> checkMethodDeclLhs _ (MethodFixity p fix pr ops) =
>   return (InfixDecl p fix pr ops)
> checkMethodDeclLhs _ (MethodSig p fs ty) =
>   return (TypeSig p fs (QualTypeExpr [] ty))
> checkMethodDeclLhs env (MethodDecl p f eqs) = checkEquationLhs True env p eqs

> checkMethods :: QualIdent -> [P Ident] -> [P Ident] -> [Decl a] -> Error ()
> checkMethods cls ops fs ds =
>   reportDuplicates duplicatePrecedence repeatedPrecedence (ops ++ ops') &&>
>   reportDuplicates duplicateDefinition repeatedDefinition fs' &&>
>   mapE_ (\(P p f) -> errorAt p (undefinedMethod cls f))
>         (filter (`notElem` fs) (ops' ++ fs'))
>   where fs' = [P p f | FunctionDecl p f _ <- ds]
>         ops' = concatMap vars (filter isInfixDecl ds)

> checkMethodDeclRhs :: VarEnv -> Decl a -> Error (MethodDecl a)
> checkMethodDeclRhs _ (InfixDecl p fix pr ops) =
>   return (MethodFixity p fix pr ops)
> checkMethodDeclRhs _ (TypeSig p fs (QualTypeExpr _ ty)) =
>   return (MethodSig p fs ty)
> checkMethodDeclRhs env (FunctionDecl p f eqs) =
>   checkArity p f eqs &&>
>   liftE (MethodDecl p f) (mapE (checkEquation env) eqs)
> checkMethodDeclRhs _ _ = internalError "checkMethodDeclRhs"

\end{verbatim}
The syntax checker examines the optional import specification of
foreign function declarations. For functions using the \texttt{ccall}
calling convention, the syntax from the Haskell 98 foreign function
interface addendum~\cite{Chakravarty03:FFI} is supported, except for
\texttt{wrapper} specifications, which are not recognized because
callbacks into Curry are not yet supported by the runtime system.
\begin{verbatim}

> checkForeign :: Position -> Ident -> CallConv -> Maybe String
>              -> Error (Maybe String)
> checkForeign _ _ CallConvPrimitive ie = return ie
> checkForeign p f CallConvCCall ie =
>   maybe (checkFunName f >> return Nothing)
>         (impEnt . words . join . break ('&' ==))
>         ie
>   where join (cs,[]) = cs
>         join (cs,c':cs') = cs ++ [' ',c',' '] ++ cs'
>         impEnt ie = kind ie >> return (Just (unwords ie))
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
>   liftE (FunLhs f) (mapE (checkConstrTerm p env) ts)
> checkLhsTerm p env (OpLhs t1 op t2) =
>   liftE2 (flip OpLhs op) (checkConstrTerm p env t1) (checkConstrTerm p env t2)
> checkLhsTerm p env (ApLhs lhs ts) =
>   liftE2 ApLhs (checkLhsTerm p env lhs) (mapE (checkConstrTerm p env) ts)

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
>     ts' <- mapE (checkConstrTerm p env) ts
>     env' <- checkBoundVars p env ts'
>     return (env',ts')

> checkBoundVars :: QuantExpr t => Position -> VarEnv -> t -> Error VarEnv
> checkBoundVars p env ts =
>   do
>     mapE_ (errorAt p . duplicateVariable . fst) (duplicates bvs)
>     return (foldr (bindVar . P p) (nestEnv env) bvs)
>   where bvs = bv ts

> checkConstrTerm :: Position -> VarEnv -> ConstrTerm a -> Error (ConstrTerm a)
> checkConstrTerm _ _ (LiteralPattern a l) = return (LiteralPattern a l)
> checkConstrTerm _ _ (NegativePattern a l) = return (NegativePattern a l)
> checkConstrTerm p env (VariablePattern a v)
>   | v == anonId = return (VariablePattern a v)
>   | otherwise = checkConstrTerm p env (ConstructorPattern a (qualify v) [])
> checkConstrTerm p env (ConstructorPattern a c ts) =
>   liftE2 ($)
>          (case qualLookupNestEnv c env of
>             [Constr _] -> return (ConstructorPattern a c)
>             rs
>               | any isConstr rs -> errorAt p (ambiguousData rs c)
>               | not (isQualified c) && null ts ->
>                   return (const (VariablePattern a (unqualify c)))
>               | otherwise -> errorAt p (undefinedData c))
>          (mapE (checkConstrTerm p env) ts)
> checkConstrTerm p env (InfixPattern a t1 op t2) =
>   liftE3 ($)
>          (case qualLookupNestEnv op env of
>             [Constr _] -> return (flip (InfixPattern a) op)
>             rs
>               | any isConstr rs -> errorAt p (ambiguousData rs op)
>               | otherwise -> errorAt p (undefinedData op))
>          (checkConstrTerm p env t1)
>          (checkConstrTerm p env t2)
> checkConstrTerm p env (ParenPattern t) =
>   liftE ParenPattern (checkConstrTerm p env t)
> checkConstrTerm p env (TuplePattern ts) =
>   liftE TuplePattern (mapE (checkConstrTerm p env) ts)
> checkConstrTerm p env (ListPattern a ts) =
>   liftE (ListPattern a) (mapE (checkConstrTerm p env) ts)
> checkConstrTerm p env (AsPattern v t) =
>   checkVars "@ pattern" p env [v] &&>
>   liftE (AsPattern v) (checkConstrTerm p env t)
> checkConstrTerm p env (LazyPattern t) =
>   liftE LazyPattern (checkConstrTerm p env t)

> checkRhs :: VarEnv -> Rhs a -> Error (Rhs a)
> checkRhs env (SimpleRhs p e ds) =
>   do
>     (env',ds') <- checkLocalDecls env ds
>     e' <- checkExpr p env' e
>     return (SimpleRhs p e' ds')
> checkRhs env (GuardedRhs es ds) =
>   do
>     (env',ds') <- checkLocalDecls env ds
>     es' <- mapE (checkCondExpr env') es
>     return (GuardedRhs es' ds')

> checkCondExpr :: VarEnv -> CondExpr a -> Error (CondExpr a)
> checkCondExpr env (CondExpr p g e) =
>   liftE2 (CondExpr p) (checkExpr p env g) (checkExpr p env e)

> checkExpr :: Position -> VarEnv -> Expression a -> Error (Expression a)
> checkExpr _ _ (Literal a l) = return (Literal a l)
> checkExpr p env (Variable a v) =
>   case qualLookupNestEnv v env of
>     [] -> errorAt p (undefinedVariable v)
>     [Constr _] -> return (Constructor a v)
>     [Var _] -> return (Variable a v)
>     rs -> errorAt p (ambiguousIdent rs v)
> checkExpr p env (Constructor a c) = checkExpr p env (Variable a c)
> checkExpr p env (Paren e) = liftE Paren (checkExpr p env e)
> checkExpr p env (Typed e ty) = liftE (flip Typed ty) (checkExpr p env e)
> checkExpr p env (Tuple es) = liftE Tuple (mapE (checkExpr p env) es)
> checkExpr p env (List a es) = liftE (List a) (mapE (checkExpr p env) es)
> checkExpr p env (ListCompr e qs) =
>   do
>     (env',qs') <- mapAccumM (checkStatement p) env qs
>     e' <- checkExpr p env' e
>     return (ListCompr e' qs')
> checkExpr p env (EnumFrom e) = liftE EnumFrom (checkExpr p env e)
> checkExpr p env (EnumFromThen e1 e2) =
>   liftE2 EnumFromThen (checkExpr p env e1) (checkExpr p env e2)
> checkExpr p env (EnumFromTo e1 e2) =
>   liftE2 EnumFromTo (checkExpr p env e1) (checkExpr p env e2)
> checkExpr p env (EnumFromThenTo e1 e2 e3) =
>   liftE3 EnumFromThenTo
>          (checkExpr p env e1)
>          (checkExpr p env e2)
>          (checkExpr p env e3)
> checkExpr p env (UnaryMinus e) = liftE UnaryMinus (checkExpr p env e)
> checkExpr p env (Apply e1 e2) =
>   liftE2 Apply (checkExpr p env e1) (checkExpr p env e2)
> checkExpr p env (InfixApply e1 op e2) =
>   liftE3 InfixApply
>          (checkExpr p env e1)
>          (checkOp p env op)
>          (checkExpr p env e2)
> checkExpr p env (LeftSection e op) =
>   liftE2 LeftSection (checkExpr p env e) (checkOp p env op)
> checkExpr p env (RightSection op e) =
>   liftE2 RightSection (checkOp p env op) (checkExpr p env e)
> checkExpr p env (Lambda ts e) =
>   do
>     (env',ts') <- checkArgs p env ts
>     e' <- checkExpr p env' e
>     return (Lambda ts' e')
> checkExpr p env (Let ds e) =
>   do
>     (env',ds') <- checkLocalDecls env ds
>     e' <- checkExpr p env' e
>     return (Let ds' e')
> checkExpr p env (Do sts e) =
>   do
>     (env',sts') <- mapAccumM (checkStatement p) env sts
>     e' <- checkExpr p env' e
>     return (Do sts' e')
> checkExpr p env (IfThenElse e1 e2 e3) =
>   liftE3 IfThenElse
>          (checkExpr p env e1)
>          (checkExpr p env e2)
>          (checkExpr p env e3)
> checkExpr p env (Case e alts) =
>   liftE2 Case (checkExpr p env e) (mapE (checkAlt env) alts)

> checkStatement :: Position -> VarEnv -> Statement a
>                -> Error (VarEnv,Statement a)
> checkStatement p env (StmtExpr e) =
>   do
>     e' <- checkExpr p env e
>     return (env,StmtExpr e')
> checkStatement p env (StmtBind t e) =
>   do
>     e' <- checkExpr p env e
>     (env',t') <- checkArg p env t
>     return (env',StmtBind t' e')
> checkStatement p env (StmtDecl ds) =
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
>     [Var _] -> return (InfixOp (attr op) v)
>     rs -> errorAt p (ambiguousIdent rs v)
>   where v = opName op
>         attr (InfixOp a _) = a
>         attr (InfixConstr a _) = a

\end{verbatim}
Auxiliary definitions.
\begin{verbatim}

> constrs :: TopDecl a -> [P Ident]
> constrs (DataDecl _ _ _ _ cs _) = map constr cs
>   where constr (ConstrDecl p _ c _) = P p c
>         constr (ConOpDecl p _ _ op _) = P p op
> constrs (NewtypeDecl _ _ _ _ (NewConstrDecl p c _) _) = [P p c]
> constrs (TypeDecl _ _ _ _) = []
> constrs (ClassDecl _ _ _ _ _) = []
> constrs (InstanceDecl _ _ _ _ _) = []
> constrs (BlockDecl _) = []

> mthds :: TopDecl a -> [P Ident]
> mthds (DataDecl _ _ _ _ _ _) = []
> mthds (NewtypeDecl _ _ _ _ _ _) = []
> mthds (TypeDecl _ _ _ _) = []
> mthds (ClassDecl _ _ _ _ ds) = [P p f | MethodSig p fs _ <- ds, f <- fs]
> mthds (InstanceDecl _ _ _ _ _) = []
> mthds (BlockDecl _) = []

> vars :: Decl a -> [P Ident]
> vars (InfixDecl p _ _ ops) = map (P p) ops
> vars (TypeSig p fs _) = map (P p) fs
> vars (FunctionDecl p f _) = [P p f]
> vars (ForeignDecl p _ _ f _) = [P p f]
> vars (PatternDecl p t _) = map (P p) (bv t)
> vars (FreeDecl p vs) = map (P p) vs
> vars (TrustAnnot p _ fs) = maybe [] (map (P p)) fs

\end{verbatim}
Due to the lack of a capitalization convention in Curry, it is
possible that an identifier may ambiguously refer to a data
constructor and a function provided that both are imported from some
other module. When checking whether an identifier denotes a
constructor there are two options with regard to ambiguous
identifiers:
\begin{enumerate}
\item Handle the identifier as a data constructor if at least one of
  the imported names is a data constructor.
\item Handle the identifier as a data constructor only if all imported
  entities are data constructors.
\end{enumerate}
We have chosen the first option because otherwise a redefinition of a
constructor can become possible by importing a function with the same
name.
\begin{verbatim}

> isDataConstr :: VarEnv -> Ident -> Bool
> isDataConstr env v =
>   any isConstr (lookupNestEnv v (globalEnv (toplevelEnv env)))

> isConstr :: ValueKind -> Bool
> isConstr (Constr _) = True
> isConstr (Var _) = False

> classMthds :: QualIdent -> TypeEnv -> [Ident]
> classMthds cls tEnv =
>   case qualLookupTopEnv cls tEnv of
>     [Class _ fs] -> fs
>     _ -> internalError "classMthds"

\end{verbatim}
Error messages.
\begin{verbatim}

> reportDuplicates :: Eq a => (a -> String) -> (a -> String) -> [P a]
>                  -> Error ()
> reportDuplicates f1 f2 xs =
>   mapE_ (\(x,xs) -> zipWithE_ report (f1 : repeat f2) (x:xs)) (duplicates xs)
>   where report f (P p x) = errorAt p (f x)

> undefinedVariable :: QualIdent -> String
> undefinedVariable v = qualName v ++ " is undefined"

> undefinedData :: QualIdent -> String
> undefinedData c = "Undefined data constructor " ++ qualName c

> undefinedMethod :: QualIdent -> Ident -> String
> undefinedMethod cls f = name f ++ " is not a method of class " ++ qualName cls

> ambiguousIdent :: [ValueKind] -> QualIdent -> String
> ambiguousIdent rs
>   | any isConstr rs = ambiguousData rs
>   | otherwise = ambiguousVariable rs

> ambiguousVariable :: [ValueKind] -> QualIdent -> String
> ambiguousVariable = ambiguous "variable"

> ambiguousData :: [ValueKind] -> QualIdent -> String
> ambiguousData = ambiguous "data constructor"

> ambiguous :: String -> [ValueKind] -> QualIdent -> String
> ambiguous what rs x = show $
>   text "Ambiguous" <+> text what <+> ppQIdent x $$
>   fsep (text "Could refer to:" :
>         punctuate comma (map (ppQIdent . origName) rs))

> duplicateDefinition :: Ident -> String
> duplicateDefinition v = name v ++ " defined more than once"

> repeatedDefinition :: Ident -> String
> repeatedDefinition v = "Redefinition of " ++ name v

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

> nonVariable :: String -> Ident -> String
> nonVariable what c =
>   "Data constructor " ++ name c ++ " used in left hand side of " ++ what

> noBody :: Ident -> String
> noBody v = name v ++ " is undefined in this scope"

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
