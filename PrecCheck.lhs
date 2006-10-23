% -*- LaTeX -*-
% $Id: PrecCheck.lhs 1980 2006-10-23 20:13:04Z wlux $
%
% Copyright (c) 2001-2006, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{PrecCheck.lhs}
\section{Checking Precedences of Infix Operators}
The parser does not know the relative precedences of infix operators
and therefore parses them as if they all associate to the right and
have the same precedence. After syntax checking, the compiler is going
to check all infix applications in the module and rearrange them
according to the relative precedences of the operators involved.
\begin{verbatim}

> module PrecCheck(precCheck,precCheckGoal) where
> import Base
> import Error
> import TopEnv

\end{verbatim}
For each declaration group, the compiler extends the precedence
environment using the fixity declarations from that scope. As a minor
optimization, we ignore all fixity declarations that assign the
default precedence to an operator.
\begin{verbatim}

> bindPrecs :: ModuleIdent -> [Decl] -> PEnv -> PEnv
> bindPrecs m ds pEnv = foldr bindPrec pEnv ds
>   where bindPrec (InfixDecl _ fix pr ops) pEnv
>           | p == defaultP = pEnv
>           | otherwise = foldr (bindP m p) pEnv ops
>           where p = OpPrec fix pr
>         bindPrec _ pEnv = pEnv

> bindP :: ModuleIdent -> OpPrec -> Ident -> PEnv -> PEnv
> bindP m p op = bindTopEnv m op (PrecInfo (qualifyWith m op) p)

\end{verbatim}
With the help of the precedence environment, the compiler checks all
infix applications and sections in the program. This pass will modify
the parse tree such that for nested infix applications the operator
with the lowest precedence becomes the root and that two adjacent
operators with the same precedence will not have conflicting
associativities. The top-level precedence environment is returned
because it is used for constructing the module's interface.
\begin{verbatim}

> precCheck :: ModuleIdent -> PEnv -> [TopDecl] -> Error (PEnv,[TopDecl])
> precCheck m pEnv ds =
>   do
>     ds' <- mapE (checkTopDecl m pEnv') ds
>     return (pEnv',ds')
>   where pEnv' = bindPrecs m [d | BlockDecl d <- ds] pEnv

> precCheckGoal :: PEnv -> Goal -> Error Goal
> precCheckGoal pEnv (Goal p e ds) =
>   liftE2 (Goal p) (checkExpr m p pEnv' e) (mapE (checkDecl m pEnv') ds)
>   where m = emptyMIdent
>         pEnv' = bindPrecs m ds pEnv

> checkTopDecl :: ModuleIdent -> PEnv -> TopDecl -> Error TopDecl
> checkTopDecl m pEnv (BlockDecl d) = liftE BlockDecl (checkDecl m pEnv d)
> checkTopDecl _ _ d = return d

> checkDecl :: ModuleIdent -> PEnv -> Decl -> Error Decl
> checkDecl m pEnv (FunctionDecl p f eqs) =
>   liftE (FunctionDecl p f) (mapE (checkEqn m pEnv) eqs)
> checkDecl m pEnv (PatternDecl p t rhs) =
>   liftE2 (PatternDecl p) (checkConstrTerm p pEnv t) (checkRhs m pEnv rhs)
> checkDecl _ _ d = return d

> checkEqn :: ModuleIdent -> PEnv -> Equation -> Error Equation
> checkEqn m pEnv (Equation p lhs rhs) =
>   liftE2 (Equation p) (checkLhs p pEnv lhs) (checkRhs m pEnv rhs)

> checkLhs :: Position -> PEnv -> Lhs -> Error Lhs
> checkLhs p pEnv (FunLhs f ts) =
>   liftE (FunLhs f) (mapE (checkConstrTerm p pEnv) ts)
> checkLhs p pEnv (OpLhs t1 op t2) =
>   liftE2 (flip OpLhs op)
>          (do
>             t1' <- checkConstrTerm p pEnv t1
>             checkOpL p pEnv op t1'
>             return t1')
>          (do
>             t2' <- checkConstrTerm p pEnv t2
>             checkOpR p pEnv op t2'
>             return t2')
> checkLhs p pEnv (ApLhs lhs ts) =
>   liftE2 ApLhs (checkLhs p pEnv lhs) (mapE (checkConstrTerm p pEnv) ts)

> checkConstrTerm :: Position -> PEnv -> ConstrTerm -> Error ConstrTerm
> checkConstrTerm _ _ (LiteralPattern l) = return (LiteralPattern l)
> checkConstrTerm _ _ (NegativePattern l) = return (NegativePattern l)
> checkConstrTerm _ _ (VariablePattern v) = return (VariablePattern v)
> checkConstrTerm p pEnv (ConstructorPattern c ts) =
>   liftE (ConstructorPattern c) (mapE (checkConstrTerm p pEnv) ts)
> checkConstrTerm p pEnv (InfixPattern t1 op t2) =
>   do
>     (t1',t2') <-
>       liftE (,) (checkConstrTerm p pEnv t1) &&& checkConstrTerm p pEnv t2
>     fixPrecT p pEnv t1' op t2'
> checkConstrTerm p pEnv (ParenPattern t) =
>   liftE ParenPattern (checkConstrTerm p pEnv t)
> checkConstrTerm p pEnv (TuplePattern ts) =
>   liftE TuplePattern (mapE (checkConstrTerm p pEnv) ts)
> checkConstrTerm p pEnv (ListPattern ts) =
>   liftE ListPattern (mapE (checkConstrTerm p pEnv) ts)
> checkConstrTerm p pEnv (AsPattern v t) =
>   liftE (AsPattern v) (checkConstrTerm p pEnv t)
> checkConstrTerm p pEnv (LazyPattern t) =
>   liftE LazyPattern (checkConstrTerm p pEnv t)

> checkRhs :: ModuleIdent -> PEnv -> Rhs -> Error Rhs
> checkRhs m pEnv (SimpleRhs p e ds) =
>   liftE2 (SimpleRhs p) (checkExpr m p pEnv' e) (mapE (checkDecl m pEnv') ds)
>   where pEnv' = bindPrecs m ds pEnv
> checkRhs m pEnv (GuardedRhs es ds) =
>   liftE2 GuardedRhs
>          (mapE (checkCondExpr m pEnv') es)
>          (mapE (checkDecl m pEnv') ds)
>   where pEnv' = bindPrecs m ds pEnv

> checkCondExpr :: ModuleIdent -> PEnv -> CondExpr -> Error CondExpr
> checkCondExpr m pEnv (CondExpr p g e) =
>   liftE2 (CondExpr p) (checkExpr m p pEnv g) (checkExpr m p pEnv e)

> checkExpr :: ModuleIdent -> Position -> PEnv -> Expression -> Error Expression
> checkExpr _ _ _ (Literal l) = return (Literal l)
> checkExpr _ _ _ (Variable v) = return (Variable v)
> checkExpr _ _ _ (Constructor c) = return (Constructor c)
> checkExpr m p pEnv (Paren e) = liftE Paren (checkExpr m p pEnv e)
> checkExpr m p pEnv (Typed e ty) = liftE (flip Typed ty) (checkExpr m p pEnv e)
> checkExpr m p pEnv (Tuple es) = liftE Tuple (mapE (checkExpr m p pEnv) es)
> checkExpr m p pEnv (List es) = liftE List (mapE (checkExpr m p pEnv) es)
> checkExpr m p pEnv (ListCompr e qs) =
>   liftE2 ListCompr (checkExpr m p pEnv' e) (mapE (checkStmt m p pEnv') qs)
>   where pEnv' = bindPrecs m [d | StmtDecl ds <- qs, d <- ds] pEnv
> checkExpr m p pEnv (EnumFrom e) = liftE EnumFrom (checkExpr m p pEnv e)
> checkExpr m p pEnv (EnumFromThen e1 e2) =
>   liftE2 EnumFromThen (checkExpr m p pEnv e1) (checkExpr m p pEnv e2)
> checkExpr m p pEnv (EnumFromTo e1 e2) =
>   liftE2 EnumFromTo (checkExpr m p pEnv e1) (checkExpr m p pEnv e2)
> checkExpr m p pEnv (EnumFromThenTo e1 e2 e3) =
>   liftE3 EnumFromThenTo
>          (checkExpr m p pEnv e1)
>          (checkExpr m p pEnv e2)
>          (checkExpr m p pEnv e3)
> checkExpr m p pEnv (UnaryMinus op e) =
>   liftE (UnaryMinus op) (checkExpr m p pEnv e)
> checkExpr m p pEnv (Apply e1 e2) =
>   liftE2 Apply (checkExpr m p pEnv e1) (checkExpr m p pEnv e2)
> checkExpr m p pEnv (InfixApply e1 op e2) =
>   do
>     (e1',e2') <- liftE (,) (checkExpr m p pEnv e1) &&& checkExpr m p pEnv e2
>     fixPrec p pEnv e1' op e2'
> checkExpr m p pEnv (LeftSection e op) =
>   do
>     e' <- checkExpr m p pEnv e
>     checkLSection p pEnv op e'
>     return (LeftSection e' op)
> checkExpr m p pEnv (RightSection op e) =
>   do
>     e' <- checkExpr m p pEnv e
>     checkRSection p pEnv op e'
>     return (RightSection op e')
> checkExpr m p pEnv (Lambda ts e) =
>   liftE2 Lambda (mapE (checkConstrTerm p pEnv) ts) (checkExpr m p pEnv e)
> checkExpr m p pEnv (Let ds e) =
>   liftE2 Let (mapE (checkDecl m pEnv') ds) (checkExpr m p pEnv' e)
>   where pEnv' = bindPrecs m ds pEnv
> checkExpr m p pEnv (Do sts e) =
>   liftE2 Do (mapE (checkStmt m p pEnv') sts) (checkExpr m p pEnv' e)
>   where pEnv' = bindPrecs m [d | StmtDecl ds <- sts, d <- ds] pEnv
> checkExpr m p pEnv (IfThenElse e1 e2 e3) =
>   liftE3 IfThenElse
>          (checkExpr m p pEnv e1)
>          (checkExpr m p pEnv e2)
>          (checkExpr m p pEnv e3)
> checkExpr m p pEnv (Case e alts) =
>   liftE2 Case (checkExpr m p pEnv e) (mapE (checkAlt m pEnv) alts)

> checkStmt :: ModuleIdent -> Position -> PEnv -> Statement -> Error Statement
> checkStmt m p pEnv (StmtExpr e) = liftE StmtExpr (checkExpr m p pEnv e)
> checkStmt m _ pEnv (StmtDecl ds) = liftE StmtDecl (mapE (checkDecl m pEnv) ds)
> checkStmt m p pEnv (StmtBind t e) =
>   liftE2 StmtBind (checkConstrTerm p pEnv t) (checkExpr m p pEnv e)

> checkAlt :: ModuleIdent -> PEnv -> Alt -> Error Alt
> checkAlt m pEnv (Alt p t rhs) =
>   liftE2 (Alt p) (checkConstrTerm p pEnv t) (checkRhs m pEnv rhs)

\end{verbatim}
The functions \texttt{fixPrec}, \texttt{fixUPrec}, and
\texttt{fixRPrec} check the relative precedences of adjacent infix
operators in nested infix applications and unary negations. The
expressions will be reordered such that the infix operator with the
lowest precedence becomes the root of the expression. \emph{The
functions rely on the fact that the parser constructs infix
applications in a right-associative fashion}, i.e., the left
argument of an infix application is never an infix application. In
addition, a unary negation never has an infix application as its
argument.

The function \texttt{fixPrec} checks whether the left argument of an
infix application is a unary negation and eventually reorders the
expression if the precedence of the infix operator is higher than that
of unary negation. This is done with the help of the function
\texttt{fixUPrec}. In any case, the function \texttt{fixRPrec} is used
for fixing the precedence of the infix operator and that of its right
argument. Note that both arguments already have been checked before
\texttt{fixPrec} is called.
\begin{verbatim}

> fixPrec :: Position -> PEnv -> Expression -> InfixOp -> Expression
>         -> Error Expression
> fixPrec p pEnv (UnaryMinus uop e1) op e2
>   | pr < 6 || pr == 6 && fix == InfixL =
>       fixRPrec p pEnv (UnaryMinus uop e1) op e2
>   | pr > 6 = fixUPrec p pEnv uop e1 op e2
>   | otherwise = errorAt p $ ambiguousParse "unary" (qualify uop) (opName op)
>   where OpPrec fix pr = opPrec op pEnv
> fixPrec p pEnv e1 op e2 = fixRPrec p pEnv e1 op e2

> fixUPrec :: Position -> PEnv -> Ident -> Expression -> InfixOp -> Expression
>          -> Error Expression
> fixUPrec p pEnv _ _ op (UnaryMinus uop _) =
>   errorAt p $ ambiguousParse "operator" (opName op) (qualify uop)
> fixUPrec p pEnv uop e1 op1 (InfixApply e2 op2 e3)
>   | pr2 < 6 || pr2 == 6 && fix2 == InfixL =
>       do
>         e' <- fixUPrec p pEnv uop e1 op1 e2
>         return (InfixApply e' op2 e3)
>   | pr2 > 6 =
>       liftE (UnaryMinus uop) (fixRPrec p pEnv e1 op1 (InfixApply e2 op2 e3))
>   | otherwise = errorAt p $ ambiguousParse "unary" (qualify uop) (opName op2)
>   where OpPrec fix1 pr1 = opPrec op1 pEnv
>         OpPrec fix2 pr2 = opPrec op2 pEnv
> fixUPrec _ _ uop e1 op e2 = return (UnaryMinus uop (InfixApply e1 op e2))

> fixRPrec :: Position -> PEnv -> Expression -> InfixOp -> Expression
>          -> Error Expression
> fixRPrec p pEnv e1 op (UnaryMinus uop e2)
>   | pr < 6 = return (InfixApply e1 op (UnaryMinus uop e2))
>   | otherwise =
>       errorAt p $ ambiguousParse "operator" (opName op) (qualify uop)
>   where OpPrec _ pr = opPrec op pEnv
> fixRPrec p pEnv e1 op1 (InfixApply e2 op2 e3)
>   | pr1 < pr2 || pr1 == pr2 && fix1 == InfixR && fix2 == InfixR =
>       return (InfixApply e1 op1 (InfixApply e2 op2 e3))
>   | pr1 > pr2 || pr1 == pr2 && fix1 == InfixL && fix2 == InfixL =
>       do
>         e' <- fixPrec p pEnv e1 op1 e2
>         return (InfixApply e' op2 e3)
>   | otherwise =
>       errorAt p $ ambiguousParse "operator" (opName op1) (opName op2)
>   where OpPrec fix1 pr1 = opPrec op1 pEnv
>         OpPrec fix2 pr2 = opPrec op2 pEnv
> fixRPrec _ _ e1 op e2 = return (InfixApply e1 op e2)

\end{verbatim}
The functions \texttt{checkLSection} and \texttt{checkRSection} are
used for handling the precedences inside left and right sections.
These functions only need to check that an infix operator occurring in
the section has either a higher precedence than the section operator
or both operators have the same precedence and are both left
associative for a left section and right associative for a right
section, respectively.
\begin{verbatim}

> checkLSection :: Position -> PEnv -> InfixOp -> Expression -> Error ()
> checkLSection p pEnv op (UnaryMinus uop _)
>   | pr < 6 || pr == 6 && fix == InfixL = return ()
>   | otherwise = errorAt p $ ambiguousParse "unary" (qualify uop) (opName op)
>   where OpPrec fix pr = opPrec op pEnv
> checkLSection p pEnv op1 (InfixApply _ op2 _)
>   | pr1 < pr2 || pr1 == pr2 && fix1 == InfixL && fix2 == InfixL = return ()
>   | otherwise =
>       errorAt p $ ambiguousParse "operator" (opName op1) (opName op2)
>   where OpPrec fix1 pr1 = opPrec op1 pEnv
>         OpPrec fix2 pr2 = opPrec op2 pEnv
> checkLSection _ _ _ _ = return ()

> checkRSection :: Position -> PEnv -> InfixOp -> Expression -> Error ()
> checkRSection p pEnv op (UnaryMinus uop _)
>   | pr < 6 = return ()
>   | otherwise = errorAt p $ ambiguousParse "unary" (qualify uop) (opName op)
>   where OpPrec _ pr = opPrec op pEnv
> checkRSection p pEnv op1 (InfixApply _ op2 _)
>   | pr1 < pr2 || pr1 == pr2 && fix1 == InfixR && fix2 == InfixR = return ()
>   | otherwise =
>       errorAt p $ ambiguousParse "operator" (opName op1) (opName op2)
>   where OpPrec fix1 pr1 = opPrec op1 pEnv
>         OpPrec fix2 pr2 = opPrec op2 pEnv
> checkRSection _ _ _ _ = return ()

\end{verbatim}
The functions \texttt{fixPrecT} and \texttt{fixRPrecT} check the
relative precedences of adjacent infix operators in patterns. The
patterns will be reordered such that the infix operator with the
lowest precedence becomes the root of the term. \emph{The functions
rely on the fact that the parser constructs infix patterns in a
right-associative fashion}, i.e., the left argument of an infix
pattern is never an infix pattern. The functions also check whether
the left and right arguments of an infix pattern are negative
literals. In that case, the operator's precedence must be lower than
that of unary negation.
\begin{verbatim}

> fixPrecT :: Position -> PEnv -> ConstrTerm -> QualIdent -> ConstrTerm
>          -> Error ConstrTerm
> fixPrecT p pEnv t1@(NegativePattern l) op t2
>   | pr < 6 || pr == 6 && fix == InfixL = fixRPrecT p pEnv t1 op t2
>   | otherwise = errorAt p $ invalidParse "unary" (negOp l) op
>   where OpPrec fix pr = prec op pEnv
> fixPrecT p pEnv t1 op t2 = fixRPrecT p pEnv t1 op t2

> fixRPrecT :: Position -> PEnv -> ConstrTerm -> QualIdent -> ConstrTerm
>           -> Error ConstrTerm
> fixRPrecT p pEnv t1 op t2@(NegativePattern l)
>   | pr < 6 = return (InfixPattern t1 op t2)
>   | otherwise = errorAt p $ invalidParse "unary" (negOp l) op
>   where OpPrec _ pr = prec op pEnv
> fixRPrecT p pEnv t1 op1 (InfixPattern t2 op2 t3)
>   | pr1 < pr2 || pr1 == pr2 && fix1 == InfixR && fix2 == InfixR =
>       return (InfixPattern t1 op1 (InfixPattern t2 op2 t3))
>   | pr1 > pr2 || pr1 == pr2 && fix1 == InfixL && fix2 == InfixL =
>       do
>         t' <- fixPrecT p pEnv t1 op1 t2
>         return (InfixPattern t' op2 t3)
>   | otherwise = errorAt p $ ambiguousParse "operator" op1 op2
>   where OpPrec fix1 pr1 = prec op1 pEnv
>         OpPrec fix2 pr2 = prec op2 pEnv
> fixRPrecT _ _ t1 op t2 = return (InfixPattern t1 op t2)

> negOp :: Literal -> Ident
> negOp (Int _) = minusId
> negOp (Float _) = fminusId
> negOp _ = internalError "negOp"

\end{verbatim}
The functions \texttt{checkOpL} and \texttt{checkOpR} check the left
and right arguments of an operator declaration. If they are infix
patterns they must bind more tightly than the operator, otherwise the
left-hand side of the declaration is invalid.
\begin{verbatim}

> checkOpL :: Position -> PEnv -> Ident -> ConstrTerm -> Error ()
> checkOpL p pEnv op (NegativePattern l)
>   | pr < 6 || pr == 6 && fix == InfixL = return ()
>   | otherwise = errorAt p $ invalidParse "unary" (negOp l) (qualify op)
>   where OpPrec fix pr = prec (qualify op) pEnv
> checkOpL p pEnv op1 (InfixPattern _ op2 _)
>   | pr1 < pr2 || pr1 == pr2 && fix1 == InfixL && fix2 == InfixL = return ()
>   | otherwise = errorAt p $ invalidParse "operator" op1 op2
>   where OpPrec fix1 pr1 = prec (qualify op1) pEnv
>         OpPrec fix2 pr2 = prec op2 pEnv
> checkOpL _ _ _ _ = return ()

> checkOpR :: Position -> PEnv -> Ident -> ConstrTerm -> Error ()
> checkOpR p pEnv op (NegativePattern l)
>   | pr < 6 = return ()
>   | otherwise = errorAt p $ invalidParse "unary" (negOp l) (qualify op)
>   where OpPrec _ pr = prec (qualify op) pEnv
> checkOpR p pEnv op1 (InfixPattern _ op2 _)
>   | pr1 < pr2 || pr1 == pr2 && fix1 == InfixR && fix2 == InfixR = return ()
>   | otherwise = errorAt p $ invalidParse "operator" op1 op2
>   where OpPrec fix1 pr1 = prec (qualify op1) pEnv
>         OpPrec fix2 pr2 = prec op2 pEnv
> checkOpR _ _ _ _ = return ()

\end{verbatim}
The functions \texttt{opPrec} and \texttt{prec} return the
associativity and operator precedence of an entity. Even though
precedence checking is performed after the renaming phase, we have to
be prepared for ambiguous identifiers here. This may happen while
checking the root of an operator definition that shadows an imported
definition.
\begin{verbatim}

> opPrec :: InfixOp -> PEnv -> OpPrec
> opPrec op = prec (opName op)

> prec :: QualIdent -> PEnv -> OpPrec
> prec op env =
>   case qualLookupTopEnv op env of
>     [] -> defaultP
>     PrecInfo _ p : _ -> p

\end{verbatim}
Error messages.
\begin{verbatim}

> invalidParse :: String -> Ident -> QualIdent -> String
> invalidParse what op1 op2 =
>   "Invalid use of " ++ what ++ " " ++ name op1 ++ " with " ++ qualName op2

> ambiguousParse :: String -> QualIdent -> QualIdent -> String
> ambiguousParse what op1 op2 =
>   "Ambiguous use of " ++ what ++ " " ++ qualName op1 ++
>   " with " ++ qualName op2

\end{verbatim}
