% -*- LaTeX -*-
% $Id: DTransform.lhs 3292 2016-07-30 12:55:31Z wlux $
%
% Copyright (c) 2001-2002, Rafael Caballero
% Copyright (c) 2003-2016, Wolfgang Lux
%
% 2002/04/10 19:00:00 Added emptyNode as constructor in type cTree
\nwfilename{DTransform.lhs}

\section{Transforming Intermediate Representation for Debugging}\label{sec:dtrans}

The purpose of this module is to convert the intermediate representation of 
a program $P$, of type {\tt Module} into the intermediate representation of a 
transformed program $P'$. 
$P'$ corresponds to the transformation of $P$ for debugging purposes. Each 
function in $P'$ computes the same values as its corresponding function in $P$,
but in addition it also returns a suitable {\em Computation Tree} representing
the computation.

\begin{verbatim}

> module DTransform(dTransform, dAddMain) where
> import IL
> import List
> import Maybe
> import PredefIdent

\end{verbatim}

All the new and auxiliary names in the transformed module will have 
\texttt{debugPrefix}
prefix to avoid conflicts with user-names. Auxiliary data types and functions
will be imported from the debug prelude, whose name is defined below, and that
will be imported by all the transformed modules.

\begin{verbatim}

> debugPrefix,debugFunctionName,debugIOFunctionName :: String
> debugPrefix         = "_debug#"
> debugFunctionName   =  "startDebugging"
> debugIOFunctionName =  "startIODebugging"

\end{verbatim}

Next is the principal  function of the module. The argument function
\texttt{trusted} returns \texttt{True} for all functions of the module
that must be trusted. These functions will return empty nodes as
computation trees, but still can include some useful trees as
children.

\begin{verbatim}

> dTransform :: (QualIdent -> Bool) -> Module -> Module
> dTransform trusted (Module m es is ds) =
>   Module m es' is' (ds' ++ generateAuxFuncs m (numAuxFuncs m ds'))
>   where ms = m:is
>         es' = map (debugRenameExport (constrs ds)) es
>         is' = imp preludeMIdent ++ imp debugPreludeMIdent ++ is
>         ds' = debugDecls trusted m ds
>         imp m = [m | m `notElem` ms]
>         constrs ds = [c | DataDecl _ _ cs <- ds, ConstrDecl c _ <- cs]
>         debugRenameExport cs x = if x `elem` cs then x else debugRenameqId x

\end{verbatim}

The debugging transformation is applied independently to each
declaration in the module. Type declarations are not changed by the
transformation except for the types of higher order arguments of data
constructors, which are transformed in order to ensure a type correct
transformed program. Function declarations are changed by the program
transformation. Finally, foreign function declarations cannot be
transformed at all, but a wrapper function pairing the result of the
foreign function with a suitable computation tree is introduced for
each foreign function.

\begin{verbatim}

> debugDecls :: (QualIdent -> Bool) -> ModuleIdent -> [Decl] -> [Decl]
> debugDecls trusted m ds = concatMap (debugDecl trusted m) ds

> debugDecl :: (QualIdent -> Bool) -> ModuleIdent -> Decl -> [Decl]
> debugDecl _ _ (DataDecl tc n cs) = [DataDecl tc n cs']
>   where cs' = [ConstrDecl c (map transformType tys) | ConstrDecl c tys <- cs]
> debugDecl _ _ (TypeDecl tc n ty) = [TypeDecl tc n (transformType ty)]
> debugDecl trusted m (FunctionDecl f vs ty e) =
>   [debugFunction trusted m f vs ty e]
> debugDecl _ _ (ForeignDecl f cc s ty) = generateForeign f cc s n' ty
>   where n = typeArity ty
>         n' = if isIOType (resultType ty) then n + 1 else n

\end{verbatim}


Some auxiliary functions widely used throughout the module.

%Function that builds a qualified name from the name of the module and a string 
%standing for the name we are going to represent.
\begin{verbatim}

> newIdName :: Int -> String -> Ident
> newIdName n name = mkIdent (debugPrefix++name++show n)

> qualPreludeName :: String -> QualIdent
> qualPreludeName name = qualifyWith preludeMIdent (mkIdent name)

> debugQualPreludeName :: String -> QualIdent
> debugQualPreludeName name = qualifyWith debugPreludeMIdent (mkIdent name)

> debugFunctionqId :: QualIdent
> debugFunctionqId = debugQualPreludeName debugFunctionName

> debugIOFunctionqId :: QualIdent
> debugIOFunctionqId = debugQualPreludeName debugIOFunctionName

> debugRenameId :: Ident -> Ident
> debugRenameId ident =
>   renameIdent (mkIdent (debugPrefix ++ name ident)) (uniqueId ident)

> debugRenameqId :: QualIdent -> QualIdent
> debugRenameqId qIdent =
>   maybe qualify qualifyWith mIdent' (debugRenameId ident')
>   where (mIdent',ident') = splitQualIdent qIdent

\end{verbatim}

Qualified data types representing some useful types in the transformed program:
{\tt [a], (a,b), Char, [Char], CTree} and {\tt [Ctree]}. Also functions for
constructing expressions of the form (a,b) and the name of function 
{\tt clean}.

\begin{verbatim}

> debugTypeList :: Type -> Type
> debugTypeList t = TypeConstructor qListId [t]

> debugTypePair :: Type -> Type -> Type
> debugTypePair a b = TypeConstructor qPairId [a,b]

> debugTypeTuple :: [Type] -> Type
> debugTypeTuple ts = TypeConstructor (qTupleId (length ts)) ts

> debugTypeChar,debugTypeString :: Type
> debugTypeChar   = TypeConstructor qCharId []
> debugTypeString = debugTypeList debugTypeChar


> debugTypeCTree,debugTypeLCTree,debugTypeCleanTree,debugTypeLCleanTree :: Type
> debugTypeCTree   = TypeConstructor (debugQualPreludeName "CTree") []
> debugTypeLCTree  = debugTypeList debugTypeCTree
> debugTypeCleanTree = debugTypePair debugTypeString debugTypeCTree
> debugTypeLCleanTree = debugTypeList debugTypeCleanTree


> qPairId :: QualIdent
> qPairId = qTupleId 2

> debugNil :: Expression
> debugNil = Constructor qNilId 0

> debugBuildPairExp :: Expression -> Expression -> Expression
> debugBuildPairExp e1 e2 = Apply (Apply (Constructor qPairId 2) e1) e2


> debugClean :: QualIdent 
> debugClean = debugQualPreludeName "clean"


> dEvalApply :: Expression -> Expression
> dEvalApply = Apply (Function (debugQualPreludeName "dEval") 1)


> void :: Expression
> void = Constructor (debugQualPreludeName "CTreeVoid") 0

> emptyNode :: Expression -> Expression
> emptyNode children =
>   Apply (Constructor (debugQualPreludeName "EmptyCTreeNode") 1) children


> debugBuildList :: [Expression] -> Expression
> debugBuildList l = foldr (Apply . Apply (Constructor qConsId 2)) debugNil l


> node :: Expression -> Expression -> Expression -> Expression -> Expression
>      -> Expression
> node name args result number children =
>   createApply (Constructor (debugQualPreludeName "CTreeNode") 5)
>               [name, args, result, number, children]

\end{verbatim}

When compiling a goal, the debugging transformation must provide a new
main function that starts the debugging process. Depending on the
goal's type this is done by applying either
\texttt{DebugPrelude.startDebugging} or
\texttt{DebugPrelude.startIODebugging} to the transformed goal.

A subtle issue with IO goals is that the simplifier may or may not
$\eta$-expand them. Without $\eta$-expansion the transformed goal's
type is \texttt{(IO ($\tau'$,CTree), CTree)}, whereas it lacks the
outer computation tree with $\eta$-expansion, i.e., the type is just
\texttt{IO ($\tau'$,CTree)}. In order to accomodate this difference,
\texttt{debugMain} first applies \texttt{DebugPrelude.performIO} to
the transformed goal if it is a nullary function. Note that the
desugarer transforms all non-IO goals \emph{goal} into unary functions
equivalent to \texttt{\char`\\z -> z =:= }\emph{goal} when generating
code for the debugger (cf. Sect.~\ref{sec:desugar}).

\begin{verbatim}

> dAddMain :: Ident -> Module -> Module
> dAddMain goalId (Module m es is ds) =
>   Module m (mainId:es) is (FunctionDecl mainId [] mainType mainExpr : ds)
>   where (arity,ty) =
>           head [(length vs,ty) | FunctionDecl f vs ty _ <- ds, f == mainId']
>         mainId = qualifyWith m goalId
>         mainId' = qualifyWith m (debugRenameId goalId)
>         mainType = TypeConstructor qIOId [TypeConstructor qUnitId []]
>         mainExpr = debugMain arity ty (Function mainId' arity)

> debugMain :: Int -> Type -> Expression -> Expression
> debugMain arity ty
>   | arity == 0 = Apply startIODebugging . Apply debugPerformIO
>   | isIOType ty = Apply startIODebugging
>   | otherwise = Apply startDebugging
>   where startDebugging = Function debugFunctionqId 1
>         startIODebugging = Function debugIOFunctionqId 2


\end{verbatim}
The implementation of foreign functions is not known and must be
trusted. For first order foreign functions this means that the
transformed function simply should pair the result of the foreign
function with a void computation tree. Therefore, given a foreign
function $f :: \tau_1 \rightarrow \dots \rightarrow \tau_n \rightarrow
\tau$, the debugging transformation just adds an auxiliary function
$f' \, x_1 \dots x_n = (f \, x_1 \dots x_n, \texttt{Void})$ to the
program. First order foreign functions in the \texttt{IO} monad are
handled similarly, except that the computation tree is lifted into the
\texttt{IO} monad. Thus, given a foreign function $f :: \tau_1
\rightarrow \dots \rightarrow \tau_n \rightarrow \texttt{IO}\,\tau$,
the transformation defines an auxiliary function $f' \, x_1 \dots x_n
= f \, x_1 \dots x_n \;\texttt{>>=} \; \texttt{return'}$ where the
auxiliary function \texttt{return' x = (x, Void)} is defined in module
\texttt{DebugPrelude}. As a minor optimization, using the monad law
$\texttt{return}\,x \; \texttt{>>=} \; k \equiv k\,x$, we transform
the \texttt{return} primitive directly into \texttt{return'}.

Higher order foreign functions like the encapsulated search primitive
\texttt{try} or the monadic bind operator \texttt{(>>=)} cannot be
handled in that way since they can invoke arbitrary computations. In
order to integrate such functions into the program transformation
approach, suitable wrapper functions, which collect the computation
trees of the subcomputations performed by the foreign function and
return them along with the function's result, must be defined in
module \texttt{DebugPrelude}. These wrappers are then used in the
transformed program instead of the original function. Fortunately,
there is only a small number of such primitives making this approach
feasible.

\textbf{Note}: The code below assumes that the wrapper functions for
higher order primitives defined in \texttt{DebugPrelude} indeed have
the same arity as the original primitives.
\begin{verbatim}

> generateForeign :: QualIdent -> CallConv -> String -> Int -> Type -> [Decl]
> generateForeign f cc s n ty = FunctionDecl f' vs ty' e : ds
>   where f' = changeFunctionqId f
>         vs = map (mkIdent . ("_"++) . show) [0..n-1]
>         ty' = transformFunType n ty
>         (e,ds) = debugForeign f cc s n (map Variable vs) ty

> debugForeign :: QualIdent -> CallConv -> String -> Int -> [Expression] -> Type
>              -> (Expression,[Decl])
> debugForeign f cc s n vs ty =
>   case foreignWrapper cc s of
>     Just f' -> (createApply (Function (debugQualPreludeName f') n) vs,[])
>     Nothing -> (debugForeign1 s ty (Function f n) vs,[ForeignDecl f cc s ty])

> debugForeign1 :: String -> Type -> Expression -> [Expression] -> Expression
> debugForeign1 s ty f vs
>   | any isFunctType (argumentTypes ty) =
>       error ("debugForeign: unknown higher order primitive " ++ s)
>   | isIOType (resultType ty) =
>       createApply preludeBind [createApply f (init vs),debugReturn,last vs]
>   | otherwise = debugBuildPairExp (createApply f vs) void
>   where preludeBind = Function (debugQualPreludeName ">>=") 3
>         debugReturn = Function (debugQualPreludeName "return'") 2
>         isFunctType ty = isArrowType ty || isIOType ty

> foreignWrapper :: CallConv -> String -> Maybe String
> foreignWrapper Primitive s
>   | s=="try"             = Just "try'"
>   | s=="return"          = Just "return'"
>   | s==">>="             = Just "bind'"
>   | s==">>"              = Just "bind_'"
>   | s=="catch"           = Just "catch'"
>   | s=="fixIO"           = Just "fixIO'"
>   | s=="encapsulate"     = Just "encapsulate'"
>   | s=="unsafePerformIO" = Just "unsafePerformIO'"
>   | otherwise            = Nothing
> foreignWrapper CCall   _ = Nothing
> foreignWrapper RawCall _ = Nothing

\end{verbatim}

Auxiliary functions are introduced to deal with higher order parameter
applications. In particular, the transformation replaces every partial
application $C\,e_1\dots e_k$ of a constructor with arity $n>k$ by an
application $@_{n-k}\;(C\,e_1\dots e_k)$ and every partial application
$f\,e_1\dots e_k$ of a (foreign or user defined) function with arity
$n>k+1$ by an application $@_{n-k-1}\;(f\,e_1\dots e_k)$. The family
of auxiliary functions $@_i$ is defined by the equations
\begin{eqnarray*}
  @_1\, f\, x &=& (f\, x, \texttt{Void}) \\
  @_{i+1}\, f\, x &=& (@_i (f x), \texttt{Void})
\end{eqnarray*}
and is necessary in order to make the transformed program type
correct.

\begin{verbatim}

> generateAuxFuncs :: ModuleIdent -> Int -> [Decl]
> generateAuxFuncs m n = map (generateAuxFunc m) [1..n]

> generateAuxFunc :: ModuleIdent -> Int -> Decl
> generateAuxFunc m i = FunctionDecl f [v1,v2] ty' e
>   where f = qIdAuxiliaryFunction m i
>         v1 = mkIdent "f"; v2 = mkIdent "x"
>         ty = foldr1 TypeArrow (map TypeVariable [0..i])
>         ty' = TypeArrow ty (transformFunType 1 ty)
>         e = debugBuildPairExp (wrapPartial m (i - 1) (apply v1 v2)) void
>         apply v1 v2 = Apply (Variable v1) (Variable v2)

> wrapPartial :: ModuleIdent -> Int -> Expression -> Expression
> wrapPartial m d
>   | d > 0 = Apply (Function (qIdAuxiliaryFunction m d) 2)
>   | otherwise = id

> qIdAuxiliaryFunction :: ModuleIdent -> Int -> QualIdent
> qIdAuxiliaryFunction m n =
>   qualifyWith m (debugRenameId (mkIdent (if n == 1 then "@" else '@':show n)))

\end{verbatim}

The compiler determines the needed auxiliary functions by looking for
applications of the form $(@_n \, e)$ in the transformed code and
computing the maximum index $n$ being used.

\begin{verbatim}

> numAuxFuncs :: ModuleIdent -> [Decl] -> Int
> numAuxFuncs m ds =
>   maximum (0 : usedAuxFuncs (qualName (qIdAuxiliaryFunction m 1)) ds)

> class AuxFuncs a where
>   usedAuxFuncs :: String -> a -> [Int]

> instance AuxFuncs a => AuxFuncs [a] where
>   usedAuxFuncs pre = concatMap (usedAuxFuncs pre)

> instance AuxFuncs Decl where
>   usedAuxFuncs _ (DataDecl _ _ _) = []
>   usedAuxFuncs _ (TypeDecl _ _ _) = []
>   usedAuxFuncs pre (FunctionDecl _ _ _ e) = usedAuxFuncs pre e
>   usedAuxFuncs _ (ForeignDecl _ _ _ _) = []

> instance AuxFuncs Expression where
>   usedAuxFuncs _ (Literal _) = []
>   usedAuxFuncs _ (Variable _) = []
>   usedAuxFuncs pre (Function f n) =
>     [index (drop (length pre) f') | n == 2 && pre `isPrefixOf` f']
>     where f' = qualName f
>           index cs = if null cs then 1 else read cs
>   usedAuxFuncs _ (Constructor _ _) = []
>   usedAuxFuncs pre (Apply e1 e2) = usedAuxFuncs pre e1 ++ usedAuxFuncs pre e2
>   usedAuxFuncs pre (Case _ e as) = usedAuxFuncs pre e ++ usedAuxFuncs pre as
>   usedAuxFuncs pre (Choice es) = usedAuxFuncs pre es
>   usedAuxFuncs pre (Exist _ e) = usedAuxFuncs pre e
>   usedAuxFuncs pre (Let _ ds e) = usedAuxFuncs pre ds ++ usedAuxFuncs pre e
>   usedAuxFuncs pre (SrcLoc _ e) = usedAuxFuncs pre e

> instance AuxFuncs Alt where
>   usedAuxFuncs pre (Alt _ e) = usedAuxFuncs pre e

> instance AuxFuncs Binding where
>   usedAuxFuncs pre (Binding _ e) = usedAuxFuncs pre e

\end{verbatim}

The function \texttt{transformFunType} transforms the type
$\tau_1 \rightarrow \dots \rightarrow \tau_n \rightarrow \tau$
of a function with arity $n$ into
$\tau'_1 \rightarrow \dots \rightarrow \tau'_n \rightarrow (\tau',\texttt{CTree})$.
The arity $n$ is passed as first argument to \texttt{transformFunType}.

The function \texttt{transformType} implements the basic
transformation of types:
\begin{displaymath}
  \begin{array}{rcll}
    \alpha' &=& \alpha \\
    \texttt{IO}\:\tau &=& \texttt{IO}\:(\tau',\texttt{CTree}) \\
    C\,\tau_1\dots\tau_n &=& C\,\tau'_1\dots\tau'_n & (C\not=\texttt{IO}) \\
    (\mu \rightarrow \nu)' &=& \mu' \rightarrow (\nu',\texttt{CTree})
  \end{array}
\end{displaymath}
Note the special case for \texttt{IO}, which is necessary in order to
implement debugging for actions. Recall that $\texttt{IO}\:\tau$ is
equivalent to $\textit{World} \rightarrow (\tau,\textit{World})$ for
some abstract representation \textit{World} of the state of the
external world. With the standard rules, this type would be
transformed into
$\textit{World} \rightarrow ((\tau',\textit{World}), \texttt{CTree})$.
Since this is no longer an instance of \texttt{IO}, this would mean
that we cannot use the standard runtime system primitives in order to
implement the primitives transformed for debugging. Therefore, we
prefer using the isomorphic type
$\textit{World} \rightarrow ((\tau',\texttt{CTree}), \textit{World})$
for transforming the type \texttt{IO}, giving rise to the special case
for \texttt{IO}.
\begin{verbatim}

> transformFunType :: Int -> Type -> Type
> transformFunType 0 ty = debugTypePair (transformType ty) debugTypeCTree
> transformFunType _ ty@(TypeArrow ty1 (TypeConstructor tc [ty2,ty3]))
>   | tc == qPairId && ty1 == TypeConstructor qWorldId [] && ty1 == ty3 =
>       transformType ty
> transformFunType n (TypeArrow ty1 ty2) =
>   TypeArrow (transformType ty1) (transformFunType (n-1) ty2)
> transformFunType _ ty = transformType ty

> transformType :: Type -> Type
> transformType (TypeArrow ty1 (TypeConstructor tc [ty2,ty3]))
>   | tc == qPairId && ty1 == TypeConstructor qWorldId [] && ty1 == ty3 =
>       TypeArrow ty1 (TypeConstructor tc [transformFunType 0 ty2,ty3])
> transformType ty@(TypeArrow _ _) = transformFunType 1 ty
> transformType (TypeConstructor tc tys)
>   | tc `elem` [qPtrId,qFunPtrId,qStablePtrId] = TypeConstructor tc tys
>   | tc == qIOId && length tys == 1 =
>       TypeConstructor tc [transformFunType 0 (head tys)]
>   | otherwise = TypeConstructor tc (map transformType tys)
> transformType (TypeVariable v) = TypeVariable v

> typeArity :: Type -> Int
> typeArity ty = length (argumentTypes ty)

> argumentTypes :: Type -> [Type]
> argumentTypes (TypeArrow ty1 (TypeConstructor tc [ty2,ty3]))
>   | tc == qPairId && ty1 == TypeConstructor qWorldId [] && ty1 == ty3 = []
> argumentTypes (TypeArrow ty1 ty2) = ty1 : argumentTypes ty2
> argumentTypes _                   = []

> resultType :: Type -> Type
> resultType (TypeArrow ty1 (TypeConstructor tc [ty2,ty3]))
>   | tc == qPairId && ty1 == TypeConstructor qWorldId [] && ty1 == ty3 =
>       TypeConstructor qIOId [ty2]
> resultType (TypeArrow _ ty) = resultType ty
> resultType ty               = ty

> isIOType :: Type -> Bool
> isIOType (TypeArrow ty1 (TypeConstructor tc [_,ty2])) =
>   tc == qPairId && ty1 == TypeConstructor qWorldId [] && ty1 == ty2
> isIOType (TypeConstructor tc [_]) = tc == qIOId
> isIOType _                        = False

> isArrowType :: Type -> Bool
> isArrowType (TypeArrow ty1 (TypeConstructor tc [_,ty2])) =
>   not (tc == qPairId && ty1 == TypeConstructor qWorldId [] && ty1 == ty2)
> isArrowType (TypeArrow _ _) = True
> isArrowType _               = False

> qWorldId :: QualIdent
> qWorldId = qualify (mkIdent "World")

\end{verbatim}

The transformation of user defined functions is performed in two
phases.

\begin{verbatim}

> debugFunction :: (QualIdent -> Bool) -> ModuleIdent
>               -> QualIdent -> [Ident] -> Type -> Expression -> Decl
> debugFunction trusted m f vs ty e = FunctionDecl f' vs ty' e'
>   where f' = changeFunctionqId f
>         ty' = transformFunType (length vs) ty
>         e' = debugSecondPhase m f (trusted f) vs ty' (debugFirstPhase e)

> changeFunctionqId :: QualIdent -> QualIdent
> changeFunctionqId f = debugRenameqId f

\end{verbatim}

The first phase of the transformation process changes the names of all
function applications.

\begin{verbatim}

> debugFirstPhase :: Expression -> Expression
> debugFirstPhase = renameFunction

> class FirstPhase a where
>   renameFunction :: a -> a

> instance FirstPhase a => FirstPhase [a] where
>   renameFunction = map renameFunction

> instance FirstPhase Expression where
>   renameFunction (Literal l) = Literal l
>   renameFunction (Variable v) = Variable v
>   renameFunction (Function f n) = Function (changeFunctionqId f) n
>   renameFunction (Constructor c n) = Constructor c n
>   renameFunction (Apply e1 e2) = Apply (renameFunction e1) (renameFunction e2)
>   renameFunction (Case rf e as) =
>     Case rf (renameFunction e) (renameFunction as)
>   renameFunction (Choice es) = Choice (renameFunction es)
>   renameFunction (Exist vs e) = Exist vs (renameFunction e)
>   renameFunction (Let rec ds e) =
>     Let rec (renameFunction ds) (renameFunction e)
>   renameFunction (SrcLoc p e) = SrcLoc p (renameFunction e)

> instance FirstPhase Alt where
>   renameFunction (Alt t e) = Alt t (renameFunction e)

> instance FirstPhase Binding where
>   renameFunction (Binding v e) = Binding v (renameFunction e)

\end{verbatim}

The second phase transforms the rules of the original functions. All
partial applications of functions and constructors have been replaced
by auxiliary functions. Also, the type of the function has been
transformed.
We only need:
\begin{itemize}
\item Introduce local definitions replacing function calls.
\item Guess if the function is a lifted function, in order to build an 
      appropriate name and include only the function variables in the node.
\end{itemize}

A special case handles $\eta$-expanded functions with result type
\texttt{IO}~$t$. According to the special transformation rule that
applies to the \texttt{IO} type (see notes on \texttt{transformFunType}),
we must not add a computation tree to the result of the transformed
function, but rather make the transformed function return the
computation tree together with its result in the \texttt{IO} monad.
Thus, an $\eta$-expanded \texttt{IO} function $f \, x_1 \dots x_{n-1}
\, x_n = e \, x_{n}$ is transformed into $f' \, x_1 \dots x_{n-1} \,
x_n = \texttt{performIO} \, e' \, x_n$ where $e'$ is the transformed
expression derived for $e$ and the auxiliary function
\texttt{performIO}, which is defined in \texttt{DebugPrelude}, takes
care of evaluating the transformed monadic action and returning a
suitable computation tree. Its definition is
\begin{verbatim}
  performIO (m,t1) = m >>= \(r,t2) -> return (r, ioCTree t1 (r,t2))
\end{verbatim}
The auxiliary function \texttt{ioCTree}, which is also defined in
\texttt{DebugPrelude}, simply adds the pair \texttt{(dEval r,t2)} to
the list of subcomputations of the computation tree \texttt{t1}.
\begin{verbatim}

> debugSecondPhase :: ModuleIdent -> QualIdent -> Bool -> [Ident] -> Type
>                  -> Expression -> Expression
> debugSecondPhase m f trust vs ty e
>   | isIOType (resultType ty) && length vs > typeArity ty =
>       newLocalDeclarationsEtaIO m f trust vs e
>   | otherwise = newLocalDeclarations m f trust vs e

> newLocalDeclarations :: ModuleIdent -> QualIdent -> Bool -> [Ident]
>                      -> Expression -> Expression
> newLocalDeclarations m f trust vs e = snd (newBindings createNode m "" [] 0 e)
>   where createNode = if trust then createEmptyNode else createTree f vs

> newLocalDeclarationsEtaIO :: ModuleIdent -> QualIdent -> Bool -> [Ident]
>                           -> Expression -> Expression
> newLocalDeclarationsEtaIO m f trust vs e =
>   etaExpandIO (newLocalDeclarations m f trust (init vs) e') v
>   where (e',v) = etaReduceIO e

> etaExpandIO :: Expression -> Expression -> Expression
> etaExpandIO (Case rf e as) = Case rf e . zipWith etaExpandIOAlt as . repeat
>   where etaExpandIOAlt (Alt t e) = Alt t . etaExpandIO e
> etaExpandIO (Exist vs e)   = Exist vs . etaExpandIO e
> etaExpandIO (Let rec ds e) = Let rec ds . etaExpandIO e
> etaExpandIO (SrcLoc p e)   = SrcLoc p . etaExpandIO e
> etaExpandIO e              = Apply (Apply debugPerformIO e)

> etaReduceIO :: Expression -> (Expression,Expression)
> etaReduceIO (Apply e1 e2)  = (e1, e2)
> etaReduceIO (Case rf e1 [Alt t e2]) = (Case rf e1 [Alt t e2'], v)
>                                                where (e2', v) = etaReduceIO e2
> etaReduceIO (Exist vs e)   = (Exist vs e', v)   where (e', v) = etaReduceIO e
> etaReduceIO (Let rec ds e) = (Let rec ds e', v) where (e', v) = etaReduceIO e
> etaReduceIO (SrcLoc p e)   = (SrcLoc p e', v)   where (e', v) = etaReduceIO e
> etaReduceIO e = error ("etaReduceIO " ++ showsPrec 11 e "")

> debugPerformIO :: Expression
> debugPerformIO = Function (debugQualPreludeName "performIO") 1

\end{verbatim}

This type represents the result of the next set of functions. The
first part is a list with the new computation trees introduced,
prepared for function \texttt{clean}, the second is a context for the
transformed expression with the new local definitions (bindings)
introduced. The third component is the transformed expression itself
(without the new local definitions).

\begin{verbatim}

> type SecondPhaseResult a = (Int,[Expression],Context,a)
> type Context = Expression -> Expression

\end{verbatim}

The next function changes an expression \texttt{e} into \texttt{case e
of \lb{}(result$N$, tree$N$) -> result$N$\rb{}}, when \texttt{e}
occurs in a strict position, and into \texttt{let \lb{} aux$N$ = e
\rb{} in let \lb{} result$N$ = fst e; tree$N$ = snd e \rb{} in
result$N$}, when \texttt{e} occurs in a lazy position. $N$ represents
a number used to ensure distinct names of variables. Actually this
information is returned in the following, more convenient format: 
\texttt{(Trees++[cleanTree], lets, Variable resultId)}, where
\texttt{cleanTree} is \texttt{(dVal result$N$, tree$N$)} and
\texttt{lets} is the context for the transformed expression, i.e.,
either the case expression without its body or the local declarations
of \texttt{aux$N$}, \texttt{result$N$}, and \texttt{tree$N$}.

\begin{verbatim}

> data Mode = Strict | Lazy

> decomposeExp :: Mode -> Int -> Expression -> SecondPhaseResult Expression
>
> decomposeExp Strict n exp = (n+1,[cleanTree],match,Variable resultId)
>   where resultId  = newIdName n "result"
>         treeId    = newIdName n "tree"
>         pattern   = ConstructorPattern qPairId [resultId,treeId]
>         match     = Case Rigid exp . return . Alt pattern
>         cleanTree = retrieveCleanTree resultId treeId
> decomposeExp Lazy n exp = (n+1,[cleanTree],lets,Variable resultId)
>   where auxId     = newIdName n "Aux"
>         resultId  = newIdName n "result"
>         treeId    = newIdName n "tree"
>         fst       = Function (qualPreludeName "fst") 1
>         snd       = Function (qualPreludeName "snd") 1
>         lets      = Let NonRec [Binding auxId exp] .
>                     Let NonRec [Binding resultId (Apply fst (Variable auxId)),
>                                 Binding treeId (Apply snd (Variable auxId))]
>         cleanTree = retrieveCleanTree resultId treeId


> class SecondPhase a where
>   newBindings :: (String -> Ident -> [Expression] -> Expression)
>               -> ModuleIdent -> String -> [Expression] -> Int -> a -> (Int,a)

> instance SecondPhase Expression where
>   newBindings createNode _ p cts n e@(Literal _) =
>     composeExp createNode p n cts e
>   newBindings createNode _ p cts n e@(Variable _) =
>     composeExp createNode p n cts e
>   newBindings createNode m p cts n f@(Function _ a)
>     | a > 0 = composeExp createNode p n cts (wrapPartial m (a - 1) f)
>     | otherwise = (n2,lets1 e')
>     where (n1,cts1,lets1,v) = decomposeExp Strict n f
>           (n2,e') = composeExp createNode p n1 (cts++cts1) v
>   newBindings createNode m p cts n e@(Constructor _ a) =
>     composeExp createNode p n cts (wrapPartial m a e)
>   newBindings createNode m p cts n e@(Apply _ _) = (n2,lets1 e'')
>     where (n1,cts1,lets1,e') = extractBindings Strict m n e
>           (n2,e'') = composeExp createNode p n1 (cts++cts1) e'
>   newBindings createNode m p cts n (Case rf e as) =
>     (n2,lets1 (Case rf e' as'))
>     where (n1,cts1,lets1,e') = extractBindings Strict m n e
>           (n2,as') = mapAccumL (newBindings createNode m p (cts++cts1)) n1 as
>   newBindings createNode m p cts n (Choice es) = (n',Choice es')
>     where (n',es') = mapAccumL (newBindings createNode m p cts) n es
>   newBindings createNode m p cts n (Exist vs e) = (n',Exist vs e')
>     where (n',e') = newBindings createNode m p cts n e
>   newBindings createNode m p cts n (Let rec ds e) =
>     (n2,letBindings rec lets1 ds' e')
>     where (n1,cts1,lets1,ds') = extractBindings Lazy m n ds
>           (n2,e') = newBindings createNode m p (cts++cts1) n1 e
>   newBindings createNode m _ cts n (SrcLoc p e) = (n',SrcLoc p e')
>     where (n',e') = newBindings createNode m p cts n e

> instance SecondPhase Alt where
>   newBindings createNode m p cts n (Alt t e) = (n',Alt t e')
>     where (n',e') = newBindings createNode m p cts n e

> composeExp :: (String -> Ident -> [Expression] -> Expression)
>            -> String -> Int -> [Expression] -> Expression -> (Int,Expression)
> composeExp createNode p n cts e = (n+1,e')
>   where rid = newIdName n "result"
>         tid = newIdName n "tree"
>         ct  = createNode p rid cts
>         e'  = Let NonRec [Binding rid e] $ Let NonRec [Binding tid ct] $
>               debugBuildPairExp (Variable rid) (Variable tid)


> class SecondPhaseArg a where
>   extractBindings :: Mode -> ModuleIdent -> Int -> a -> SecondPhaseResult a

> instance SecondPhaseArg a => SecondPhaseArg [a] where
>   extractBindings _    _ n []     = (n,[],id,[])
>   extractBindings mode m n (x:xs) = (n2,cts1++cts2,lets1 . lets2,x':xs')
>     where (n1,cts1,lets1,x')  = extractBindings mode m n x
>           (n2,cts2,lets2,xs') = extractBindings mode m n1 xs

> instance SecondPhaseArg Expression where
>   extractBindings mode m n e = (n2,cts1++cts2,lets1 . lets2,e')
>     where (f,es) = extractApply e []
>           (n1,cts1,lets1,es') = extractBindings Lazy m n es
>           (n2,cts2,lets2,e') = extractBindingsApply mode m n1 f es'

> instance SecondPhaseArg Binding where
>   extractBindings _ m n (Binding v e) = (n',cts',lets',Binding v e')
>     where (n',cts',lets',e') = extractBindings Lazy m n e


> extractBindingsApply :: Mode -> ModuleIdent -> Int -> Expression
>                      -> [Expression] -> SecondPhaseResult Expression

> extractBindingsApply mode _ n e@(Literal _) args = applyValue mode n e args
> extractBindingsApply mode _ n e@(Variable _) args = applyValue mode n e args
> extractBindingsApply mode m n e@(Constructor _ arity) args =
>   applyValue mode n (wrapPartial m d (createApply e args)) []
>   where d = arity - length args
> extractBindingsApply mode m n f@(Function _ arity) args
>   | d > 0 = applyValue mode n (wrapPartial m (d - 1) (createApply f args)) []
>   | otherwise = applyExp mode n (createApply f nArgs) extraArgs
>   where d = arity - length args
>         (nArgs,extraArgs) = splitAt arity args
> extractBindingsApply mode m n e@(Case _ _ _) args = applyExp mode n' e' args
>   where (n',e') = newBindings createEmptyNode m "" [] n e
> extractBindingsApply mode m n e@(Choice _) args = applyExp mode n' e' args
>   where (n',e') = newBindings createEmptyNode m "" [] n e
> extractBindingsApply mode m n (Exist vs e) args =
>   (n2,cts1++cts2,Exist vs . lets1 . lets2,e'')
>   where (n1,cts1,lets1,e') = extractBindings mode m n e
>         (n2,cts2,lets2,e'') = applyValue mode n1 e' args
> extractBindingsApply mode m n (Let rec ds e) args =
>   (n3,cts1++cts2++cts3,letBindings rec lets1 ds' . lets2 . lets3,e'')
>   where (n1,cts1,lets1,ds') = extractBindings Lazy m n ds
>         (n2,cts2,lets2,e') = extractBindings mode m n1 e
>         (n3,cts3,lets3,e'') = applyValue mode n2 e' args
> extractBindingsApply mode m n (SrcLoc p e) args =
>   (n2,cts1++cts2,lets1 . lets2,e'')
>   where (n1,cts1,lets1,e') = extractBindings mode m n e
>         (n2,cts2,lets2,e'') = applyValue mode n1 (SrcLoc p e') args

> applyValue :: Mode -> Int -> Expression -> [Expression]
>            -> SecondPhaseResult Expression
> applyValue _    n f []     = (n,[],id,f)
> applyValue mode n f (e:es) = applyExp mode n (Apply f e) es

> applyExp :: Mode -> Int -> Expression -> [Expression]
>          -> SecondPhaseResult Expression
> applyExp mode n e es = (n2,cts1++cts2,lets1 . lets2,e')
>   where (n1,cts1,lets1,v) = decomposeExp mode n e
>         (n2,cts2,lets2,e') = applyValue mode n1 v es


> extractApply :: Expression -> [Expression] -> (Expression,[Expression])
> extractApply (Apply e1 e2) l = extractApply e1 (e2:l)
> extractApply e1 l = (e1,l)

> createApply :: Expression -> [Expression] -> Expression
> createApply exp lExp = foldl Apply exp lExp


> createTree :: QualIdent -> [Ident] -> String -> Ident -> [Expression]
>            -> Expression
> createTree qId lVars rule resultId trees =
>   node fName fParams fResult fRule clean
>   where (idModule,ident) = splitQualIdent qId
>         fNameCh = maybe "" moduleName idModule ++ "." ++ show ident
>         fName   = debugBuildList (map (Literal . Char) fNameCh)
>         fParams = debugBuildList (map (dEvalApply.Variable) lVars)
>         fResult = (dEvalApply.Variable) resultId
>         fRule   = debugBuildList (map (Literal . Char) rule)
>         clean   = if null trees then debugNil
>                   else Apply (Function debugClean 1) (debugBuildList trees)

> createEmptyNode :: String -> Ident -> [Expression] -> Expression
> createEmptyNode _ _ trees = if null trees then void else emptyNode clean
>   where clean = Apply (Function debugClean 1) (debugBuildList trees)

> letBindings :: Rec -> Context -> [Binding] -> Context
> letBindings NonRec lets ds = lets . Let NonRec ds
> letBindings Rec lets ds =
>   fixLetrecBindings (Let Rec) (lets (Let Rec ds (Variable undefined)))

> fixLetrecBindings :: ([Binding]->Context) -> Expression -> Context
> fixLetrecBindings bindings (Variable _) = bindings []
> fixLetrecBindings bindings (Exist vs e) =
>   Exist vs . fixLetrecBindings bindings e
> fixLetrecBindings bindings (Let _ ds e) =
>   fixLetrecBindings (bindings . (ds++)) e

\end{verbatim}

The function \texttt{retrieveCleanTree} computes an element of the
list of computation trees of the form \texttt{(dEval $r$,$t$)} for a
given pair of variables $r$ and $t$ bound to a subcomputation result
and its associated computation tree, respectively.

\begin{verbatim}

> retrieveCleanTree :: Ident -> Ident -> Expression
> retrieveCleanTree id1 id2 =
>   debugBuildPairExp (dEvalApply (Variable id1)) (Variable id2)

\end{verbatim}
