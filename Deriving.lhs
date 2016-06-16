% -*- LaTeX -*-
% $Id: Deriving.lhs 3225 2016-06-16 08:40:29Z wlux $
%
% Copyright (c) 2006-2015, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Deriving.lhs}
\section{Derived Instances}
This module implements the code generating derived instance declarations.
\begin{verbatim}

> module Deriving(derive) where
> import Applicative
> import Base
> import Curry
> import Env
> import Error
> import InstInfo
> import List
> import Maybe
> import PrecInfo
> import PredefIdent
> import TopEnv
> import Types
> import TypeInfo
> import TypeTrans
> import Utils

> derive :: ModuleIdent -> PEnv -> TCEnv -> InstEnv -> [TopDecl ()]
>         -> Error [TopDecl ()]
> derive m pEnv tcEnv iEnv ds =
>   liftA concat (mapA (deriveInstances m pEnv tcEnv iEnv) ds)

> deriveInstances :: ModuleIdent -> PEnv -> TCEnv -> InstEnv -> TopDecl ()
>                 -> Error [TopDecl ()]
> deriveInstances m pEnv tcEnv iEnv (DataDecl _ _ tc tvs cs clss) =
>   mapA (deriveInstance m pEnv tcEnv iEnv tc tvs cs) clss
> deriveInstances m pEnv tcEnv iEnv (NewtypeDecl _ _ tc tvs nc clss) =
>   mapA (deriveInstance m pEnv tcEnv iEnv tc tvs [constrDecl nc]) clss
>   where constrDecl (NewConstrDecl p c ty) = ConstrDecl p [] [] c [ty]
>         constrDecl (NewRecordDecl p c l ty) =
>           RecordDecl p [] [] c [FieldDecl p [l] ty]
> deriveInstances _ _ _ _ _ = return []

\end{verbatim}
Instances can be derived only for a set of predefined classes. An
error is reported if the user asks for instances of other classes be
derived.
\begin{verbatim}

> type Constr = (QualIdent,Int,Maybe [Ident])

> deriveInstance :: ModuleIdent -> PEnv -> TCEnv -> InstEnv -> Ident -> [Ident]
>                -> [ConstrDecl] -> DClass -> Error (TopDecl ())
> deriveInstance m pEnv tcEnv iEnv tc tvs cs (DClass p cls) =
>   liftA (InstanceDecl p cx' cls ty' . trustAll p)
>         (deriveMethods pEnv tcEnv p (map constr cs) cls)
>   where cx = snd3 (fromJust (lookupEnv (CT cls' tc') iEnv))
>         ty = foldl TypeApply (TypeConstructor tc') tvs'
>         tc' = qualifyWith m tc
>         tvs' = take (length tvs) (map TypeVariable [0..])
>         cls' = origName (head (qualLookupTopEnv cls tcEnv))
>         QualTypeExpr cx' ty' = fromQualType tvs (QualType cx ty)
>         constr (ConstrDecl _ _ _ c tys) = (qualifyWith m c,length tys,Nothing)
>         constr (ConOpDecl _ _ _ _ op _) = (qualifyWith m op,2,Nothing)
>         constr (RecordDecl _ _ _ c fs) = (qualifyWith m c,length ls,Just ls)
>           where ls = [l | FieldDecl _ ls _ <- fs, l <- ls]
>         trustAll p ds = TrustAnnot p Trust [] : ds

> deriveMethods :: PEnv -> TCEnv -> Position -> [Constr] -> QualIdent
>               -> Error [Decl ()]
> deriveMethods pEnv tcEnv p cs cls
>   | cls' == qEqId = return (eqMethods p cs)
>   | cls' == qOrdId = return (ordMethods p cs)
>   | cls' == qEnumId = enumMethods p cs
>   | cls' == qBoundedId = boundedMethods p cs
>   | cls' == qShowId = return (showMethods pEnv p cs)
>   | otherwise = errorAt p (notDerivable cls)
>   where cls' = origName (head (qualLookupTopEnv cls tcEnv))

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

> eqMethods :: Position -> [Constr] -> [Decl ()]
> eqMethods p cs = [deriveEq nameSupply p cs]

> deriveEq :: [Ident] -> Position -> [Constr] -> Decl ()
> deriveEq (x:y:vs) p cs =
>   funDecl p eqOpId [x,y] (Case (mkVar x) (map (eqCase vs p y) cs))

> eqCase :: [Ident] -> Position -> Ident -> Constr -> Alt ()
> eqCase vs p y (c,n,ls) =
>   caseAlt p (conPattern c xs)
>           (Case (mkVar y) [eqEqCase vs' p xs (c,n,ls),eqNeqCase p])
>   where (xs,vs') = splitAt n vs

> eqEqCase :: [Ident] -> Position -> [Ident] -> Constr -> Alt ()
> eqEqCase vs p xs (c,n,_) = caseAlt p (conPattern c ys) (eqCaseArgs p xs ys)
>   where ys = take n vs

> eqNeqCase :: Position -> Alt ()
> eqNeqCase p = caseAlt p (VariablePattern () anonId) prelFalse

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

> ordMethods :: Position -> [Constr] -> [Decl ()]
> ordMethods p cs = [deriveCompare nameSupply p cs]

> deriveCompare :: [Ident] -> Position -> [Constr] -> Decl ()
> deriveCompare (x:y:vs) p cs =
>   funDecl p compareId [x,y]
>           (Case (mkVar x) (map (cmpCase vs p y) (splits cs)))
>   where splits [] = []
>         splits (x:xs) =
>           ([],x,xs) : map (\(ys,z,zs) -> (x:ys,z,zs)) (splits xs)

> cmpCase :: [Ident] -> Position -> Ident -> ([Constr],Constr,[Constr])
>         -> Alt ()
> cmpCase vs p y (csLT,(c,n,ls),csGT) =
>   caseAlt p (conPattern c xs)
>           (Case (mkVar y)
>                 (map (cmpNeqCase p prelGT) csLT ++
>                  cmpEqCase vs' p xs (c,n,ls) :
>                  map (cmpNeqCase p prelLT) csGT))
>   where (xs,vs') = splitAt n vs

> cmpEqCase :: [Ident] -> Position -> [Ident] -> Constr -> Alt ()
> cmpEqCase vs p xs (c,n,_) = caseAlt p (conPattern c ys) (cmpCaseArgs p xs ys)
>   where ys = take n vs

> cmpNeqCase :: Position -> Expression () -> Constr -> Alt ()
> cmpNeqCase p z (c,n,_) = caseAlt p (conPattern c (replicate n anonId)) z

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
> isEnum (c:cs) = all ((0 ==) . snd3) (c:cs)

> enumMethods :: Position -> [Constr] -> Error [Decl ()]
> enumMethods p cs
>   | isEnum cs = return [succ,pred,toEnum,fromEnum,enumFrom,enumFromThen]
>   | otherwise = errorAt p notEnum
>   where succ = deriveSucc p cs
>         pred = derivePred p cs
>         toEnum = deriveToEnum p cs
>         fromEnum = deriveFromEnum p cs
>         enumFrom = deriveEnumFrom nameSupply p (last cs) 
>         enumFromThen = deriveEnumFromThen nameSupply p (head cs) (last cs)

> deriveSucc :: Position -> [Constr] -> Decl ()
> deriveSucc p cs =
>   FunctionDecl p () f (if null eqs then [failedEqn p f] else eqs)
>   where f = succId
>         eqs = zipWith (succEqn p f) cs (tail cs)

> derivePred :: Position -> [Constr] -> Decl ()
> derivePred p cs =
>   FunctionDecl p () f (if null eqs then [failedEqn p f] else eqs)
>   where f = predId
>         eqs = zipWith (predEqn p f) (tail cs) cs

> deriveFromEnum :: Position -> [Constr] -> Decl ()
> deriveFromEnum p cs = FunctionDecl p () f (zipWith (fromEnumEqn p f) cs [0..])
>   where f = fromEnumId

> deriveToEnum :: Position -> [Constr] -> Decl ()
> deriveToEnum p cs = FunctionDecl p () f (zipWith (toEnumEqn p f) [0..] cs)
>   where f = toEnumId

> deriveEnumFrom :: [Ident] -> Position -> Constr -> Decl ()
> deriveEnumFrom (x:_) p (c,n,_) =
>   funDecl p enumFromId [x] (prelEnumFromTo (mkVar x) (Constructor () c))

> deriveEnumFromThen :: [Ident] -> Position -> Constr -> Constr -> Decl ()
> deriveEnumFromThen (x:y:_) p c1 c2 =
>   funDecl p enumFromThenId [x,y]
>           (prelEnumFromThenTo (mkVar x) (mkVar y) (enumBound x y c1 c2))

> enumBound :: Ident -> Ident -> Constr -> Constr -> Expression ()
> enumBound x y (c1,_,_) (c2,_,_) =
>   IfThenElse (prelLeq (prelFromEnum (mkVar x)) (prelFromEnum (mkVar y)))
>              (Constructor () c2)
>              (Constructor () c1)

> failedEqn :: Position -> Ident -> Equation ()
> failedEqn p f = equation p f [VariablePattern () anonId] prelFailed

> succEqn :: Position -> Ident -> Constr -> Constr -> Equation ()
> succEqn p f (c1,_,_) (c2,_,_) =
>   equation p f [ConstructorPattern () c1 []] (Constructor () c2)

> predEqn :: Position -> Ident -> Constr -> Constr -> Equation ()
> predEqn p f (c1,_,_) (c2,_,_) =
>   equation p f [ConstructorPattern () c1 []] (Constructor () c2)

> toEnumEqn :: Position -> Ident -> Integer -> Constr -> Equation ()
> toEnumEqn p f i (c,_,_) =
>   equation p f [LiteralPattern () (Integer i)] (Constructor () c)

> fromEnumEqn :: Position -> Ident -> Constr -> Integer -> Equation ()
> fromEnumEqn p f (c,_,_) i =
>   equation p f [ConstructorPattern () c []] (Literal () (Integer i))

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

> boundedMethods :: Position -> [Constr] -> Error [Decl ()]
> boundedMethods p cs
>   | isBounded cs = return [minBound,maxBound]
>   | otherwise = errorAt p notBounded
>   where minBound = deriveMinBound p (head cs)
>         maxBound = deriveMaxBound p (last cs)

> deriveMinBound :: Position -> Constr -> Decl ()
> deriveMinBound p (c,n,_) =
>   funDecl p minBoundId [] $
>   apply (Constructor () c) (replicate n prelMinBound)

> deriveMaxBound :: Position -> Constr -> Decl ()
> deriveMaxBound p (c,n,_) =
>   funDecl p maxBoundId [] $
>   apply (Constructor () c) (replicate n prelMaxBound)

\end{verbatim}
\paragraph{String Representation}
Instances of \texttt{Show} can be derived for all data and renaming
types. We derive only an implementation of \texttt{showsPrec} and rely
on the default implementations of \texttt{show} and \texttt{showList}.
The derived \texttt{showsPrec} uses record notation if the constructor
was declared with field labels (unless the field list is empty) and
otherwise uses infix notation for infix constructor applications
adding parentheses only where needed and ignoring associativity
 (cf.\ Chap.~10 of~\cite{PeytonJones03:Haskell}). Note that in contrast
to the \texttt{show} function in the current Curry report,
\texttt{showsPrec} is a flexible function. For instance,
\texttt{let x :: Bool; x free in show x} non-deterministically binds
\texttt{x} to one of the constants \verb|False| and \verb|True| and
returns its string representation \verb|"False"| and \verb|"True"|,
respectively.
\begin{verbatim}

> showMethods :: PEnv -> Position -> [Constr] -> [Decl ()]
> showMethods pEnv p cs = [deriveShowsPrec pEnv nameSupply p cs]

> deriveShowsPrec :: PEnv -> [Ident] -> Position -> [Constr] -> Decl ()
> deriveShowsPrec pEnv vs p cs =
>   FunctionDecl p () showsPrecId (map (showsPrecEqn pEnv vs p showsPrecId) cs)

> showsPrecEqn :: PEnv -> [Ident] -> Position -> Ident -> Constr -> Equation ()
> showsPrecEqn pEnv (v:vs) p f (c,n,ls) =
>   equation p f (showsPrecMatch v c ls xs) (showsPrecExpr pEnv v c ls xs)
>   where xs = take n vs

> showsPrecMatch :: Ident -> QualIdent -> Maybe [Ident] -> [Ident]
>                -> [ConstrTerm ()]
> showsPrecMatch v c ls xs =
>   [VariablePattern () (if null xs || isJust ls then anonId else v),
>    ConstructorPattern () c (map (VariablePattern ()) xs)]

> showsPrecExpr :: PEnv -> Ident -> QualIdent -> Maybe [Ident] -> [Ident]
>               -> Expression ()
> showsPrecExpr pEnv v c ls xs
>   | null xs = showsPrecShowString (showsCon c' "")
>   | isJust ls = showsPrecShowFields c' (fromJust ls) xs 
>   | isInfixOp c' && length xs == 2 =
>       showsPrecShowParen v p (showsPrecShowInfixApp p c' xs)
>   | otherwise = showsPrecShowParen v 10 (showsPrecShowApp 10 c' xs)
>   where c' = unqualify c
>         OpPrec _ p = prec c pEnv

> showsCon :: Ident -> ShowS
> showsCon c = showParen (isInfixOp c) (showString (name c))

> showsPrecShowString :: String -> Expression ()
> showsPrecShowString s = prelShowString (Literal () (String s))

> showsPrecShowParen :: Ident -> Integer -> Expression () -> Expression ()
> showsPrecShowParen v p =
>   prelShowParen (prelGt (mkVar v) (Literal () (Integer p)))

> showsPrecShowApp :: Integer -> Ident -> [Ident] -> Expression ()
> showsPrecShowApp p c xs =
>   foldr1 prelDot $
>   showsPrecShowString (showsCon c " ") :
>   intersperse (prelShowChar (Literal () (Char ' ')))
>               (map (showsPrecShowArg p) xs)

> showsPrecShowInfixApp :: Integer -> Ident -> [Ident] -> Expression ()
> showsPrecShowInfixApp p op xs =
>   foldr1 prelDot $
>   intersperse (showsPrecShowString (' ' : name op ++ " "))
>               (map (showsPrecShowArg p) xs)

> showsPrecShowArg :: Integer -> Ident -> Expression ()
> showsPrecShowArg p = prelShowsPrec (Literal () (Integer (p + 1))) . mkVar

> showsPrecShowFields :: Ident -> [Ident] -> [Ident] -> Expression ()
> showsPrecShowFields c ls xs =
>   foldr ($)
>         (showsPrecShowString "}")
>         (zipWith3 showsPrecShowField (showsCon c " {" : repeat ", ") ls xs)

> showsPrecShowField :: String -> Ident -> Ident -> Expression ()
>                    -> Expression ()
> showsPrecShowField pre l x =
>   (showsPrecShowString (pre ++ showsCon l " = ") `prelDot`) .
>   (showsPrecShowArg 0 x `prelDot`)

> prec :: QualIdent -> PEnv -> OpPrec
> prec op env =
>   case qualLookupTopEnv op env of
>     [] -> defaultPrec
>     PrecInfo _ p : _ -> p

\end{verbatim}
\paragraph{Auxiliary functions}
\begin{verbatim}

> conPattern :: QualIdent -> [Ident] -> ConstrTerm ()
> conPattern c vs = ConstructorPattern () c (map (VariablePattern ()) vs)

> funDecl :: Position -> Ident -> [Ident] -> Expression () -> Decl ()
> funDecl p f vs e =
>   FunctionDecl p () f [equation p f (map (VariablePattern ()) vs) e]

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

> prelFailed :: Expression ()
> prelFailed = Variable () qFailed

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

> failedId, dotOpId, eqOpId, leqOpId, gtOpId, andOpId, compareId :: Ident
> succId, predId, fromEnumId, toEnumId, enumFromId, enumFromThenId :: Ident
> minBoundId, maxBoundId :: Ident
> showsPrecId, showParenId, showCharId, showStringId :: Ident
> failedId = mkIdent "failed"
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

> qFailed :: QualIdent
> qFailed = qualifyWith preludeMIdent failedId

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
