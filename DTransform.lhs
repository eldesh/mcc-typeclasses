% -*- LaTeX -*-
% $Id: DTransform.lhs 2955 2010-06-12 22:40:11Z wlux $
%
% Copyright (c) 2001-2002, Rafael Caballero
% Copyright (c) 2003-2010, Wolfgang Lux
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
> dTransform trusted (Module m is ds) = Module m is' ds'
>   where ms = m:is
>         is' = imp preludeMIdent ++ imp debugPreludeMIdent ++ is
>         ds' = debugDecls trusted ds
>         imp m = [m | m `notElem` ms]

\end{verbatim}

The debugging transformation is applied independently to each
declaration in the module. Type declarations are not changed by the
transformation except for the types of higher order arguments of data
constructors, which are transformed in order to ensure a type correct
transformed program. In addition, auxiliary functions are introduced
to handle partial applications of the data constructors. Function
declarations are changed by the program transformation and auxiliary
functions are introduced for their partial applications, too. Finally,
foreign function declarations cannot be transformed at all, but a
wrapper function pairing the result of the foreign function with a
suitable computation tree is introduced for each foreign function.
Auxiliary functions for partial applications of the foreign functions
are provided as well.

\begin{verbatim}

> data SymbolType = IsFunction | IsConstructor deriving (Eq,Show)

> debugDecls :: (QualIdent -> Bool) -> [Decl] -> [Decl]
> debugDecls trusted ds = concatMap (debugDecl trusted) ds

> debugDecl :: (QualIdent -> Bool) -> Decl -> [Decl]
> debugDecl _ (DataDecl tc n cs) = DataDecl tc n cs' : concat ds'
>   where (cs',ds') = unzip (map (debugConstrDecl ty0) cs)
>         ty0 = TypeConstructor tc (map TypeVariable [0..n-1])
> debugDecl _ (TypeDecl tc n ty) = [TypeDecl tc n (transformType ty)]
> debugDecl trusted (FunctionDecl f vs ty e) =
>   generateAuxFuncs (f,IsFunction,length vs,ty) ++
>   [debugFunction trusted f vs ty e]
> debugDecl _ (ForeignDecl f cc s ty) =
>   generateAuxFuncs (f,IsFunction,n',ty) ++
>   generateForeign f cc s n' ty
>   where n = typeArity ty
>         n' = if isIOType (resultType ty) then n + 1 else n
> debugDecl _ SplitAnnot = [SplitAnnot]

> debugConstrDecl :: Type -> ConstrDecl -> (ConstrDecl,[Decl])
> debugConstrDecl ty0 (ConstrDecl c tys) =
>   (ConstrDecl c (map transformType tys),
>    generateAuxFuncs (c,IsConstructor,length tys,ty))
>   where ty = normalizeType (foldr TypeArrow ty0 tys)

> normalizeType :: Type -> Type
> normalizeType ty = rename (nub (tvars ty)) ty
>   where rename tvs (TypeConstructor c tys) =
>           TypeConstructor c (map (rename tvs) tys)
>         rename tvs (TypeVariable tv) =
>           TypeVariable (fromJust (elemIndex tv tvs))
>         rename tvs (TypeArrow ty1 ty2) =
>           TypeArrow (rename tvs ty1) (rename tvs ty2)
>         tvars (TypeConstructor _ tys) = concatMap tvars tys
>         tvars (TypeVariable tv) = [tv]
>         tvars (TypeArrow ty1 ty2) = tvars ty1 ++ tvars ty2

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

> debugRenameId :: String -> Ident -> Ident
> debugRenameId suffix ident =
>   renameIdent (mkIdent (debugPrefix ++ name ident ++ suffix)) (uniqueId ident)

> debugRenameqId :: String -> QualIdent -> QualIdent
> debugRenameqId suffix qIdent =
>   maybe qualify qualifyWith mIdent' (debugRenameId suffix ident')
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

> debugTypeMainAux :: Type
> debugTypeMainAux = TypeArrow (debugTypePair (TypeVariable 0) debugTypeCTree)
>                              (TypeConstructor qSuccessId [])



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
> dAddMain goalId (Module m is ds) =
>   Module m is (FunctionDecl mainId [] mainType mainExpr : ds)
>   where (arity,ty) =
>           head [(length vs,ty) | FunctionDecl f vs ty _ <- ds, f == mainId']
>         mainId = qualifyWith m goalId
>         mainId' = qualifyWith m (debugRenameId "" goalId)
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
applications. In particular, the transformation introduces $n-1$
auxiliary functions $f'_0, \dots, f'_{n-2}$ for a (foreign) function
$f$ with arity $n$. These functions are necessary in order to make the
transformed program type correct and are defined by equations $f'_i\,x
= (f'_{i+1}\,x, \texttt{Void})$, where $f'$ is used instead of
$f'_{n-1}$. For the same reason, the transformation introduces $n$
auxiliary functions $c'_0, \dots, c'_{n-1}$ for each data constructor
$c$ with arity $n$. Their definitions are similar to those of the
auxiliary functions for transformed functions except for using $c$ in
place of $c'_n$.

The next function gets the current module identifier, a qualified
identifier, a value indicating whether the identifier denotes a
function or a constructor, its arity \texttt{n}, and its type, and
generates the new auxiliary functions.

\begin{verbatim}

> generateAuxFuncs :: (QualIdent,SymbolType,Int,Type) -> [Decl]
> generateAuxFuncs (f,IsFunction,n,ty) =
>   map (generateAuxFunc f ty (Function f n)) [0..n-2]
> generateAuxFuncs (c,IsConstructor,n,ty) =
>   map (generateAuxFunc c ty (Constructor c n)) [0..n-1]

> generateAuxFunc :: QualIdent -> Type -> Expression -> Int -> Decl
> generateAuxFunc f ty e i = FunctionDecl f' vs ty' e'
>   where f' = qidAuxiliaryFunction f i
>         vs = map (mkIdent . ("_"++) . show) [0..i]
>         ty' = transformFunType (i+1) ty
>         app = debugFirstPhase (createApply e (map Variable vs))
>         e' = debugBuildPairExp app void

> qidAuxiliaryFunction :: QualIdent -> Int -> QualIdent
> qidAuxiliaryFunction f n = debugRenameqId ('#':show n) f

> extractApply :: Expression -> [Expression] -> (Expression,[Expression])
> extractApply (Apply e1 e2) l = extractApply e1 (e2:l)
> extractApply e1 l = (e1,l)

> createApply :: Expression -> [Expression] -> Expression
> createApply exp lExp = foldl Apply exp lExp

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

> debugFunction :: (QualIdent -> Bool) -> QualIdent -> [Ident] -> Type
>               -> Expression -> Decl
> debugFunction trusted f vs ty e = FunctionDecl f' vs ty' e'
>   where f' = changeFunctionqId f
>         ty' = transformFunType (length vs) ty
>         e' = debugSecondPhase f (trusted f) vs ty' (debugFirstPhase e)

> changeFunctionqId :: QualIdent -> QualIdent
> changeFunctionqId f = debugRenameqId "" f

\end{verbatim}

The first phase of the transformation process changes the names of all
function and partial constructor applications.

\begin{verbatim}

> debugFirstPhase :: Expression -> Expression
> debugFirstPhase e = firstPhase 0 e

> class FirstPhase a where
>   firstPhase :: Int -> a -> a

> instance FirstPhase a => FirstPhase [a] where
>   firstPhase d = map (firstPhase d)

> instance FirstPhase Expression where
>   firstPhase _ (Literal l) = Literal l
>   firstPhase _ (Variable v) = Variable v
>   firstPhase d (Function f n)
>     | d < n-1         = Function (qidAuxiliaryFunction f d) (d+1)
>     | otherwise       = Function (changeFunctionqId f) n
>   firstPhase d (Constructor c n)
>     | d < n     = Function (qidAuxiliaryFunction c d) (d+1)
>     | otherwise = Constructor c n
>   firstPhase d (Apply e1 e2) = Apply (firstPhase (d+1) e1) (firstPhase 0 e2)
>   firstPhase _ (Case rf e as) = Case rf (firstPhase 0 e) (firstPhase 0 as)
>   firstPhase _ (Choice es) = Choice (firstPhase 0 es)
>   firstPhase _ (Exist vs e) = Exist vs (firstPhase 0 e)
>   firstPhase _ (Let rec ds e) = Let rec (firstPhase 0 ds) (firstPhase 0 e)
>   firstPhase _ (SrcLoc p e) = SrcLoc p (firstPhase 0 e)

> instance FirstPhase Alt where
>   firstPhase d (Alt t e) = Alt t (firstPhase d e)

> instance FirstPhase Binding where
>   firstPhase d (Binding v e) = Binding v (firstPhase d e)

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

> debugSecondPhase :: QualIdent -> Bool -> [Ident] -> Type -> Expression
>                  -> Expression
> debugSecondPhase f trust vs ty e
>   | isIOType (resultType ty) && length vs > typeArity ty =
>       newLocalDeclarationsEtaIO f trust vs e
>   | otherwise = newLocalDeclarations f trust vs e

> newLocalDeclarations :: QualIdent -> Bool -> [Ident] -> Expression
>                      -> Expression
> newLocalDeclarations f trust vs e = snd (newBindings createNode "" [] 0 e)
>   where createNode = if trust then createEmptyNode else createTree f vs

> newLocalDeclarationsEtaIO :: QualIdent -> Bool -> [Ident] -> Expression
>                           -> Expression
> newLocalDeclarationsEtaIO f trust vs e =
>   etaExpandIO (newLocalDeclarations f trust (init vs) e') v
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
>               -> String -> [Expression] -> Int -> a -> (Int,a)

> instance SecondPhase Expression where
>   newBindings createNode p cts n e@(Literal _) =
>     composeExp createNode p n cts e
>   newBindings createNode p cts n e@(Variable _) =
>     composeExp createNode p n cts e
>   newBindings createNode p cts n f@(Function _ a)
>     | a > 0 = composeExp createNode p n cts f
>     | otherwise = (n2,lets1 e')
>     where (n1,cts1,lets1,v) = decomposeExp Strict n f
>           (n2,e') = composeExp createNode p n1 (cts++cts1) v
>   newBindings createNode p cts n e@(Constructor _ _) =
>     composeExp createNode p n cts e
>   newBindings createNode p cts n e@(Apply _ _) = (n2,lets1 e'')
>     where (n1,cts1,lets1,e') = extractBindings Strict n e
>           (n2,e'') = composeExp createNode p n1 (cts++cts1) e'
>   newBindings createNode p cts n (Case rf e as) = (n2,lets1 (Case rf e' as'))
>     where (n1,cts1,lets1,e') = extractBindings Strict n e
>           (n2,as') = mapAccumL (newBindings createNode p (cts++cts1)) n1 as
>   newBindings createNode p cts n (Choice es) = (n',Choice es')
>     where (n',es') = mapAccumL (newBindings createNode p cts) n es
>   newBindings createNode p cts n (Exist vs e) = (n',Exist vs e')
>     where (n',e') = newBindings createNode p cts n e
>   newBindings createNode p cts n (Let rec ds e) =
>     (n2,letBindings rec lets1 ds' e')
>     where (n1,cts1,lets1,ds') = extractBindings Lazy n ds
>           (n2,e') = newBindings createNode p (cts++cts1) n1 e
>   newBindings createNode _ cts n (SrcLoc p e) = (n',SrcLoc p e')
>     where (n',e') = newBindings createNode p cts n e

> instance SecondPhase Alt where
>   newBindings createNode p cts n (Alt t e) = (n',Alt t e')
>     where (n',e') = newBindings createNode p cts n e

> composeExp :: (String -> Ident -> [Expression] -> Expression)
>            -> String -> Int -> [Expression] -> Expression -> (Int,Expression)
> composeExp createNode p n cts e = (n+1,e')
>   where rid = newIdName n "result"
>         tid = newIdName n "tree"
>         ct  = createNode p rid cts
>         e'  = Let NonRec [Binding rid e] $ Let NonRec [Binding tid ct] $
>               debugBuildPairExp (Variable rid) (Variable tid)


> class SecondPhaseArg a where
>   extractBindings :: Mode -> Int -> a -> SecondPhaseResult a

> instance SecondPhaseArg a => SecondPhaseArg [a] where
>   extractBindings _    n []     = (n,[],id,[])
>   extractBindings mode n (x:xs) = (n2,cts1++cts2,lets1 . lets2,x':xs')
>     where (n1,cts1,lets1,x')  = extractBindings mode n x
>           (n2,cts2,lets2,xs') = extractBindings mode n1 xs

> instance SecondPhaseArg Expression where
>   extractBindings mode n e = (n2,cts1++cts2,lets1 . lets2,e')
>     where (f,es) = extractApply e []
>           (n1,cts1,lets1,es') = extractBindings Lazy n es
>           (n2,cts2,lets2,e') = extractBindingsApply mode n1 f es'

> instance SecondPhaseArg Binding where
>   extractBindings _ n (Binding v e) = (n',cts',lets',Binding v e')
>     where (n',cts',lets',e') = extractBindings Lazy n e


> extractBindingsApply :: Mode -> Int -> Expression -> [Expression]
>                      -> SecondPhaseResult Expression

> extractBindingsApply mode n e@(Literal _) args = applyValue mode n e args
> extractBindingsApply mode n e@(Variable _) args = applyValue mode n e args
> extractBindingsApply mode n e@(Constructor _ _) args =
>   applyValue mode n (createApply e args) []
> extractBindingsApply mode n f@(Function _ arity) args
>   | length args < arity = applyValue mode n (createApply f args) []
>   | otherwise = applyExp mode n (createApply f nArgs) extraArgs
>   where (nArgs,extraArgs) = splitAt arity args
> extractBindingsApply mode n e@(Case _ _ _) args = applyExp mode n' e' args
>   where (n',e') = newBindings createEmptyNode "" [] n e
> extractBindingsApply mode n e@(Choice _) args = applyExp mode n' e' args
>   where (n',e') = newBindings createEmptyNode "" [] n e
> extractBindingsApply mode n (Exist vs e) args =
>   (n2,cts1++cts2,Exist vs . lets1 . lets2,e'')
>   where (n1,cts1,lets1,e') = extractBindings mode n e
>         (n2,cts2,lets2,e'') = applyValue mode n1 e' args
> extractBindingsApply mode n (Let rec ds e) args =
>   (n3,cts1++cts2++cts3,letBindings rec lets1 ds' . lets2 . lets3,e'')
>   where (n1,cts1,lets1,ds') = extractBindings Lazy n ds
>         (n2,cts2,lets2,e') = extractBindings mode n1 e
>         (n3,cts3,lets3,e'') = applyValue mode n2 e' args
> extractBindingsApply mode n (SrcLoc p e) args =
>   (n2,cts1++cts2,lets1 . lets2,e'')
>   where (n1,cts1,lets1,e') = extractBindings mode n e
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


> createTree :: QualIdent -> [Ident] -> String -> Ident -> [Expression]
>            -> Expression
> createTree qId lVars rule resultId trees =
>   node fName fParams fResult fRule clean
>   where (idModule,ident) = splitQualIdent qId
>         fNameCh = maybe "" moduleName idModule ++ "." ++ name ident
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
