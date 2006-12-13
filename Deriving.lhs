% -*- LaTeX -*-
% $Id: Deriving.lhs 2041 2006-12-13 09:43:43Z wlux $
%
% Copyright (c) 2006, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Derive.lhs}
\section{Derived Instances}
This module implements the code generating derived instance declarations.
\begin{verbatim}

> module Deriving(derive) where
> import Base
> import Combined
> import Error
> import List
> import Monad
> import TopEnv

> type Constr = (QualIdent,Int)

> derive :: Monad m => ModuleIdent -> TCEnv -> Int -> Position -> [ClassAssert]
>        -> Ident -> [Ident] -> [ConstrDecl] -> QualIdent -> m (TopDecl ())
> derive m tcEnv n p cx tc tvs cs cls =
>   liftM (InstanceDecl p cx cls ty)
>         (run (deriveMethods tcEnv p (map constr cs) cls) n)
>   where ty = ConstructorType (qualifyWith m tc) (map VariableType tvs)
>         constr (ConstrDecl _ _ c tys) = (qualifyWith m c,length tys)
>         constr (ConOpDecl _ _ _ op _) = (qualifyWith m op,2)

> deriveMethods :: Monad m => TCEnv -> Position -> [Constr]
>               -> QualIdent -> DeriveState m [MethodDecl ()]
> deriveMethods tcEnv p cs cls
>   | cls' == qEqId = eqMethods p cs
>   | cls' == qOrdId = ordMethods p cs
>   | cls' == qEnumId = enumMethods p cs
>   | cls' == qBoundedId = boundedMethods p cs
>   | cls' == qShowId = showMethods p cs
>   | otherwise = errorAt p (notDerivable cls)
>   where cls' = origName (head (qualLookupTopEnv cls tcEnv))

\end{verbatim}
When deriving instance declarations, the compiler must introduce fresh
variables which are distinct from all other variables in the program.
Furthermore, the fresh variables must use a non-zero renaming key. For
that reason, the \texttt{derive} function must be applied to a
different renaming key for each derived instance. We use a state monad
once more for the introduction of fresh variables.
\begin{verbatim}

> type DeriveState m a = StateT [Ident] m a

> run :: Monad m => DeriveState m a -> Int -> m a
> run m n = callSt m [renameIdent (mkIdent ("_#" ++ show i)) n | i <- [1..]]

> freshIdent :: Monad m => DeriveState m Ident
> freshIdent = liftM head (updateSt tail)

> freshIdents :: Monad m => Int -> DeriveState m [Ident]
> freshIdents n = liftM (take n) (updateSt (drop n))

\end{verbatim}
\paragraph{Equality}
Instances of \texttt{Eq} can be derived trivially. The implementation
of \texttt{(==)} checks whether both arguments have identical roots
and if so goes on comparing their arguments from left to right. We do
not derive an implementation for \texttt{(/=)}, but simply rely on its
default implementation. Note that the code for \texttt{(==)} uses case
expressions for matching the two arguments. Thus, the derived method
is rigid like the polymorphic equality operator in the current Curry
report.
\begin{verbatim}

> eqMethods :: Monad m => Position -> [Constr] -> DeriveState m [MethodDecl ()]
> eqMethods p cs = sequence [deriveEq p cs]

> deriveEq :: Monad m => Position -> [Constr] -> DeriveState m (MethodDecl ())
> deriveEq p cs =
>   do
>     x <- freshIdent
>     y <- freshIdent
>     liftM (methodDecl p eqOpId [x,y] . Case (mkVar x)) (mapM (eqCase p y) cs)

> eqCase :: Monad m => Position -> Ident -> Constr -> DeriveState m (Alt ())
> eqCase p y (c,n) =
>   do
>     xs <- freshIdents n
>     liftM (caseAlt p (conPattern c xs) . Case (mkVar y))
>           (sequence [eqEqCase p xs (c,n),eqNeqCase p])

> eqEqCase :: Monad m => Position -> [Ident] -> Constr -> DeriveState m (Alt ())
> eqEqCase p xs (c,n) =
>   do
>     ys <- freshIdents n
>     return (caseAlt p (conPattern c ys) (eqCaseArgs p xs ys))

> eqNeqCase :: Monad m => Position -> DeriveState m (Alt ())
> eqNeqCase p =
>   do
>     x <- freshIdent
>     return (caseAlt p (VariablePattern () x) prelFalse)

> eqCaseArgs :: Position -> [Ident] -> [Ident] -> Expression ()
> eqCaseArgs p xs ys
>   | null xs = prelTrue
>   | otherwise = foldr1 prelAnd (zipWith prelEq (map mkVar xs) (map mkVar ys))

\end{verbatim}
\paragraph{Ordering}
Instances of \texttt{Ord} are almost as trivial as equality.
Constructors in a data type are ordered according to their occurrence
in the type definition and two terms with identical roots are ordered
according to their arguments proceeding from left to right. Just like
the derived implementation of \texttt{(==)}, the derived
implementation of \texttt{compare} is rigid in both arguments for
compatibility with the current Curry report. We do not derive
implementations for other \texttt{Ord} methods but rely on their
default implementations.

\ToDo{It might be worth deriving implementations for \texttt{(<)},
  \texttt{(>)}, \texttt{(<=)}, and \texttt{(>=)} in the case of
  enumeration types.}
\begin{verbatim}

> ordMethods :: Monad m => Position -> [Constr] -> DeriveState m [MethodDecl ()]
> ordMethods p cs = sequence [deriveCompare p cs]

> deriveCompare :: Monad m => Position -> [Constr]
>               -> DeriveState m (MethodDecl ())
> deriveCompare p cs =
>   do
>     x <- freshIdent
>     y <- freshIdent
>     liftM (methodDecl p compareId [x,y] . Case (mkVar x))
>           (mapM (cmpCase p y) (splits cs))
>   where splits [] = []
>         splits (x:xs) =
>           ([],x,xs) : map (\(ys,z,zs) -> (x:ys,z,zs)) (splits xs)

> cmpCase :: Monad m => Position -> Ident -> ([Constr],Constr,[Constr])
>         -> DeriveState m (Alt ())
> cmpCase p y (csLT,(c,n),csGT) =
>   do
>     xs <- freshIdents n
>     liftM (caseAlt p (conPattern c xs) . Case (mkVar y))
>           (sequence (map (cmpNeqCase p prelGT) csLT ++
>                      cmpEqCase p xs (c,n) : map (cmpNeqCase p prelLT) csGT))

> cmpEqCase :: Monad m => Position -> [Ident] -> Constr
>           -> DeriveState m (Alt ())
> cmpEqCase p xs (c,n) =
>   do
>     ys <- freshIdents n
>     return (caseAlt p (conPattern c ys) (cmpCaseArgs p xs ys))

> cmpNeqCase :: Monad m => Position -> Expression () -> Constr
>            -> DeriveState m (Alt ())
> cmpNeqCase p z (c,n) =
>   do
>     ys <- freshIdents n
>     return (caseAlt p (conPattern c ys) z)

> cmpCaseArgs :: Position -> [Ident] -> [Ident] -> Expression ()
> cmpCaseArgs p xs ys
>   | null xs = prelEQ
>   | otherwise = foldr1 (matchCmpResult p)
>                        (zipWith prelCompare (map mkVar xs) (map mkVar ys))

> matchCmpResult :: Position -> Expression () -> Expression () -> Expression ()
> matchCmpResult p e1 e2 =
>   Case e1
>        [caseAlt p prelLTPattern prelLT,
>         caseAlt p prelEQPattern e2,
>         caseAlt p prelGTPattern prelGT]

\end{verbatim}
\paragraph{Enumerations}
Instances of \texttt{Enum} can be derived only for enumeration types,
i.e. types where all data constructors are constants. We derive
implementations for all methods except \texttt{enumFromTo} and
\texttt{enumFromThenTo}. The implementations of \texttt{enumFrom} and
\texttt{enumFromThen} are defined in terms of those two functions by
providing appropriate upper or lower bounds for the enumerations.
This is required for enumerations of bounded types in Haskell
(cf.\ Chap.~10 of~\cite{PeytonJones03:Haskell}) and makes expressions
like \verb|[False ..]| well defined.
\begin{verbatim}

> isEnum :: [Constr] -> Bool
> isEnum [] = False
> isEnum (c:cs) = all ((0 ==) . snd) (c:cs)

> enumMethods :: Monad m => Position -> [Constr]
>             -> DeriveState m [MethodDecl ()]
> enumMethods p cs
>   | isEnum cs = sequence [succ,pred,toEnum,fromEnum,enumFrom,enumFromThen]
>   | otherwise = errorAt p notEnum
>   where succ = return (deriveSucc p cs)
>         pred = return (derivePred p cs)
>         toEnum = return (deriveToEnum p cs)
>         fromEnum = return (deriveFromEnum p cs)
>         enumFrom = deriveEnumFrom p (last cs) 
>         enumFromThen = deriveEnumFromThen p (head cs) (last cs)

> deriveSucc :: Position -> [Constr] -> MethodDecl ()
> deriveSucc p cs = MethodDecl p f (zipWith (succEqn p f) cs (tail cs))
>   where f = succId

> derivePred :: Position -> [Constr] -> MethodDecl ()
> derivePred p cs = MethodDecl p f (zipWith (predEqn p f) (tail cs) cs)
>   where f = predId

> deriveFromEnum :: Position -> [Constr] -> MethodDecl ()
> deriveFromEnum p cs = MethodDecl p f (zipWith (fromEnumEqn p f) cs [0..])
>   where f = fromEnumId

> deriveToEnum :: Position -> [Constr] -> MethodDecl ()
> deriveToEnum p cs = MethodDecl p f (zipWith (toEnumEqn p f) [0..] cs)
>   where f = toEnumId

> deriveEnumFrom :: Monad m => Position -> Constr
>                -> DeriveState m (MethodDecl ())
> deriveEnumFrom p (c,n) =
>   do
>     x <- freshIdent
>     return (methodDecl p enumFromId [x] $
>             prelEnumFromTo (mkVar x) (Constructor () c))

> deriveEnumFromThen :: Monad m => Position -> Constr -> Constr
>                    -> DeriveState m (MethodDecl ())
> deriveEnumFromThen p c1 c2 =
>   do
>     x <- freshIdent
>     y <- freshIdent
>     return (methodDecl p enumFromThenId [x,y] $
>             prelEnumFromThenTo (mkVar x) (mkVar y) (enumBound x y c1 c2))

> enumBound :: Ident -> Ident -> Constr -> Constr -> Expression ()
> enumBound x y (c1,_) (c2,_) =
>   IfThenElse (prelLeq (prelFromEnum (mkVar x)) (prelFromEnum (mkVar y)))
>              (Constructor () c2)
>              (Constructor () c1)

> succEqn :: Position -> Ident -> Constr -> Constr -> Equation ()
> succEqn p f (c1,_) (c2,_) =
>   equation p f [ConstructorPattern () c1 []] (Constructor () c2)

> predEqn :: Position -> Ident -> Constr -> Constr -> Equation ()
> predEqn p f (c1,_) (c2,_) =
>   equation p f [ConstructorPattern () c1 []] (Constructor () c2)

> toEnumEqn :: Position -> Ident -> Int -> Constr -> Equation ()
> toEnumEqn p f i (c,_) =
>   equation p f [LiteralPattern () (Int i)] (Constructor () c)

> fromEnumEqn :: Position -> Ident -> Constr -> Int -> Equation ()
> fromEnumEqn p f (c,_) i =
>   equation p f [ConstructorPattern () c []] (Literal () (Int i))

\end{verbatim}
\paragraph{Upper and Lower Bounds}
Instances of \texttt{Bounded} can be derived for enumerations and for
single constructor types. The upper and lower bounds of an enumeration
type are given by the right-most and left-most constructor of the
declaration, respectively. For a single constructor type, upper and
lower bounds are computed by determining the upper and lower bounds of
all arguments.
\begin{verbatim}

> isBounded :: [Constr] -> Bool
> isBounded cs = length cs == 1 || isEnum cs

> boundedMethods :: Monad m => Position -> [Constr]
>                -> DeriveState m [MethodDecl ()]
> boundedMethods p cs
>   | isBounded cs = return [minBound,maxBound]
>   | otherwise = errorAt p notBounded
>   where minBound = deriveMinBound p (head cs)
>         maxBound = deriveMaxBound p (last cs)

> deriveMinBound :: Position -> Constr -> MethodDecl ()
> deriveMinBound p (c,n) =
>   methodDecl p minBoundId [] $
>   apply (Constructor () c) (replicate n prelMinBound)

> deriveMaxBound :: Position -> Constr -> MethodDecl ()
> deriveMaxBound p (c,n) =
>   methodDecl p maxBoundId [] $
>   apply (Constructor () c) (replicate n prelMaxBound)

\end{verbatim}
\paragraph{String Representation}
Instances of \texttt{Show} can be derived for all data types. We
derive only an implementation of \texttt{showsPrec} and rely on the
default implementations of \texttt{show} and \texttt{showList}. Note
that in contrast to the \texttt{show} function in the current Curry
report, \texttt{showsPrec} is a flexible function. For instance,
\texttt{let x :: Bool; x free in show x} non-deterministically binds
\texttt{x} to one of the constants \verb|False| and \verb|True| and
returns its string representation \verb|"False"| and \verb|"True"|,
respectively.
\begin{verbatim}

> showMethods :: Monad m => Position -> [Constr]
>             -> DeriveState m [MethodDecl ()]
> showMethods p cs = sequence [deriveShowsPrec p cs]

> deriveShowsPrec :: Monad m => Position -> [Constr]
>                 -> DeriveState m (MethodDecl ())
> deriveShowsPrec p cs = liftM (MethodDecl p f) (mapM (showsPrecEqn p f) cs)
>   where f = showsPrecId

> showsPrecEqn :: Monad m => Position -> Ident -> Constr
>              -> DeriveState m (Equation ())
> showsPrecEqn p f (c,n) =
>   do
>     l <- freshIdent
>     xs <- freshIdents n
>     return (equation p f (showsPrecMatch l c xs) (showsPrecExpr l c xs))

> showsPrecMatch :: Ident -> QualIdent -> [Ident] -> [ConstrTerm ()]
> showsPrecMatch l c xs =
>   [VariablePattern () l,ConstructorPattern () c (map (VariablePattern ()) xs)]

> showsPrecExpr :: Ident -> QualIdent -> [Ident] -> Expression ()
> showsPrecExpr l c xs
>   | null xs = showsPrecShowString (showsCon c' "")
>   | isInfixOp c' && length xs == 2 =
>       -- FIXME: use the operator's real precedence
>       --     => need the operator precedence environment here
>       showsPrecShowParen l 9 (showsPrecShowInfixApp 9 c' xs)
>   | otherwise = showsPrecShowParen l 10 (showsPrecShowApp 10 c' xs)
>   where c' = unqualify c

> showsCon :: Ident -> ShowS
> showsCon c = showParen (isInfixOp c) (showString (name c))

> showsPrecShowString :: String -> Expression ()
> showsPrecShowString s = prelShowString (Literal () (String s))

> showsPrecShowParen :: Ident -> Int -> Expression () -> Expression ()
> showsPrecShowParen l p =
>   prelShowParen (prelGt (mkVar l) (Literal () (Int p)))

> showsPrecShowApp :: Int -> Ident -> [Ident] -> Expression ()
> showsPrecShowApp p c xs =
>   foldr1 prelDot $
>   showsPrecShowString (showsCon c " ") :
>   intersperse (prelShowChar (Literal () (Char ' ')))
>               (map (showsPrecShowArg p) xs)

> showsPrecShowInfixApp :: Int -> Ident -> [Ident] -> Expression ()
> showsPrecShowInfixApp p op xs =
>   foldr1 prelDot $
>   intersperse (showsPrecShowString ((' ' : name op ++ " ")))
>               (map (showsPrecShowArg p) xs)

> showsPrecShowArg :: Int -> Ident -> Expression ()
> showsPrecShowArg p = prelShowsPrec (Literal () (Int (p + 1))) . mkVar

\end{verbatim}
\paragraph{Auxiliary functions}
\begin{verbatim}

> conPattern :: QualIdent -> [Ident] -> ConstrTerm ()
> conPattern c vs = ConstructorPattern () c (map (VariablePattern ()) vs)

> methodDecl :: Position -> Ident -> [Ident] -> Expression () -> MethodDecl ()
> methodDecl p f vs e =
>   MethodDecl p f [equation p f (map (VariablePattern ()) vs) e]

> equation :: Position -> Ident -> [ConstrTerm a] -> Expression a -> Equation a
> equation p f ts e = Equation p (FunLhs f ts) (SimpleRhs p e [])

> caseAlt :: Position -> ConstrTerm a -> Expression a -> Alt a
> caseAlt p t e = Alt p t (SimpleRhs p e [])

> apply :: Expression a -> [Expression a] -> Expression a
> apply = foldl Apply

> mkVar :: Ident -> Expression ()
> mkVar = Variable () . qualify

> prelTrue, prelFalse :: Expression ()
> prelTrue = Constructor () qTrueId
> prelFalse = Constructor () qFalseId

> prelLT, prelEQ, prelGT :: Expression ()
> prelLT = Constructor () qLTId
> prelEQ = Constructor () qEQId
> prelGT = Constructor () qGTId

> prelLTPattern, prelEQPattern, prelGTPattern :: ConstrTerm ()
> prelLTPattern = ConstructorPattern () qLTId []
> prelEQPattern = ConstructorPattern () qEQId []
> prelGTPattern = ConstructorPattern () qGTId []

> prelFromEnum :: Expression () -> Expression ()
> prelFromEnum = Apply (Variable () qFromEnumId)

> prelEnumFromTo :: Expression () -> Expression () -> Expression ()
> prelEnumFromTo x z = apply (Variable () qEnumFromToId) [x,z]

> prelEnumFromThenTo :: Expression () -> Expression () -> Expression ()
>                    -> Expression ()
> prelEnumFromThenTo x y z = apply (Variable () qEnumFromThenToId) [x,y,z]

> prelMinBound, prelMaxBound :: Expression ()
> prelMinBound = Variable () qMinBoundId
> prelMaxBound = Variable () qMaxBoundId

> prelShowsPrec :: Expression () -> Expression () -> Expression ()
> prelShowsPrec x y = apply (Variable () qShowsPrecId) [x,y]

> prelShowParen :: Expression () -> Expression () -> Expression ()
> prelShowParen x y = apply (Variable () qShowParenId) [x,y]

> prelShowChar, prelShowString :: Expression () -> Expression ()
> prelShowChar x = apply (Variable () qShowCharId) [x]
> prelShowString x = apply (Variable () qShowStringId) [x]

> type BinOp a = Expression a -> Expression a -> Expression a

> prelDot :: BinOp ()
> prelDot = binOp qDotOpId

> prelAnd, prelEq :: BinOp ()
> prelAnd = binOp qAndOpId
> prelEq = binOp qEqOpId

> prelCompare, prelLeq, prelGt :: BinOp ()
> prelCompare = binOp qCompareId
> prelLeq = binOp qLeqOpId
> prelGt = binOp qGtOpId

> binOp :: QualIdent -> BinOp ()
> binOp op x y = InfixApply x (InfixOp () op) y

\end{verbatim}
Additional prelude identifiers.
\begin{verbatim}

> dotOpId, eqOpId, leqOpId, gtOpId, andOpId, compareId, succId, predId :: Ident
> fromEnumId, toEnumId, enumFromId, enumFromThenId :: Ident
> minBoundId, maxBoundId :: Ident
> showsPrecId, showParenId, showCharId, showStringId :: Ident
> dotOpId = mkIdent "."
> eqOpId = mkIdent "=="
> leqOpId = mkIdent "<="
> gtOpId = mkIdent ">"
> andOpId = mkIdent "&&"
> compareId = mkIdent "compare"
> succId = mkIdent "succ"
> predId = mkIdent "pred"
> fromEnumId = mkIdent "fromEnum"
> toEnumId = mkIdent "toEnum"
> enumFromId = mkIdent "enumFrom"
> enumFromToId = mkIdent "enumFromTo"
> enumFromThenId = mkIdent "enumFromThen"
> enumFromThenToId = mkIdent "enumFromThenTo"
> minBoundId = mkIdent "minBound"
> maxBoundId = mkIdent "maxBound"
> showsPrecId = mkIdent "showsPrec"
> showParenId = mkIdent "showParen"
> showCharId = mkIdent "showChar"
> showStringId = mkIdent "showString"

> qDotOpId, qAndOpId, qEqOpId, qLeqOpId, qGtOpId, qCompareId :: QualIdent
> qDotOpId = qualifyWith preludeMIdent dotOpId
> qAndOpId = qualifyWith preludeMIdent andOpId
> qEqOpId = qualifyWith preludeMIdent eqOpId
> qLeqOpId = qualifyWith preludeMIdent leqOpId
> qGtOpId = qualifyWith preludeMIdent gtOpId
> qCompareId = qualifyWith preludeMIdent compareId

> qFromEnumId, qEnumFromToId, qEnumFromThenToId :: QualIdent
> qFromEnumId = qualifyWith preludeMIdent fromEnumId
> qEnumFromToId = qualifyWith preludeMIdent enumFromToId
> qEnumFromThenToId = qualifyWith preludeMIdent enumFromThenToId

> qMinBoundId, qMaxBoundId :: QualIdent
> qMinBoundId = qualifyWith preludeMIdent minBoundId
> qMaxBoundId = qualifyWith preludeMIdent maxBoundId

> qShowsPrecId, qShowParenId, qShowCharId, qShowStringId :: QualIdent
> qShowsPrecId = qualifyWith preludeMIdent showsPrecId
> qShowParenId = qualifyWith preludeMIdent showParenId
> qShowCharId = qualifyWith preludeMIdent showCharId
> qShowStringId = qualifyWith preludeMIdent showStringId

> qLTId, qEQId, qGTId :: QualIdent
> qLTId = qualifyWith preludeMIdent (mkIdent "LT")
> qEQId = qualifyWith preludeMIdent (mkIdent "EQ")
> qGTId = qualifyWith preludeMIdent (mkIdent "GT")

\end{verbatim}
Error messages.
\begin{verbatim}

> notDerivable :: QualIdent -> String
> notDerivable cls = "Instances of " ++ qualName cls ++ " cannot be derived"

> notEnum :: String
> notEnum = "Instances for Enum can be derived only for enumeration types"

> notBounded :: String
> notBounded =
>   "Instances of Bounded can be derived only for enumeration\
>   \ and single constructor types"

\end{verbatim}
