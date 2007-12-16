% -*- LaTeX -*-
% $Id: DTransform.lhs 2570 2007-12-16 21:53:05Z wlux $
%
% Copyright (c) 2001-2002, Rafael Caballero
% Copyright (c) 2003-2007, Wolfgang Lux
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
{\tt debugPrefix}
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
> dTransform trusted (Module m is ds) =
>   Module m (debugPreludeMIdent:is) (debugDecls m trusted ds)

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

A special case handles the selector functions introduced by the
pattern binding update strategy (see p.~\pageref{pattern-binding} in
Sect.~\ref{pattern-binding}). These functions are not transformed at
all.

\begin{verbatim}

> data SymbolType = IsFunction | IsConstructor deriving (Eq,Show)

> debugDecls :: ModuleIdent -> (QualIdent -> Bool) -> [Decl] -> [Decl]
> debugDecls m trusted ds = 
>   concatMap (generateAuxFuncs m) (nub (typesPredefined ds)) ++
>   concatMap (debugDecl m trusted) ds

> debugDecl :: ModuleIdent -> (QualIdent -> Bool) -> Decl -> [Decl]
> debugDecl m _ (DataDecl tc n cs) = DataDecl tc n cs' : concat ds'
>   where (cs',ds') = unzip (map (debugConstrDecl m ty0) cs)
>         ty0 = TypeConstructor tc (map TypeVariable [0..n-1])
> debugDecl m _ (TypeDecl tc n ty) = [TypeDecl tc n (transformType' ty)]
> debugDecl m trusted (FunctionDecl f vs ty e)
>   | isQSelectorId f = [FunctionDecl f vs ty e]
>   | otherwise =
>       generateAuxFuncs m (f,IsFunction,length vs,ty) ++
>       [debugFunction m trusted f vs ty e]
> debugDecl m _ (ForeignDecl f cc s ty) =
>   generateAuxFuncs m (f,IsFunction,n',ty) ++
>   [ForeignDecl f cc s ty,generateForeign m f cc s n' ty]
>   where n = typeArity ty
>         n' = if isIOType (resultType ty) then n + 1 else n

> debugConstrDecl :: ModuleIdent -> Type -> ConstrDecl -> (ConstrDecl,[Decl])
> debugConstrDecl m ty0 (ConstrDecl c tys) =
>   (ConstrDecl c (map transformType' tys),
>    generateAuxFuncs m (c,IsConstructor,length tys,ty))
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

> debugQualPreludeName :: String -> QualIdent
> debugQualPreludeName name = qualifyWith debugPreludeMIdent (mkIdent name)

> debugFunctionqId :: QualIdent
> debugFunctionqId = debugQualPreludeName debugFunctionName

> debugIOFunctionqId :: QualIdent
> debugIOFunctionqId = debugQualPreludeName debugIOFunctionName

> debugRenameId :: String -> Ident -> Ident
> debugRenameId suffix ident =
>   renameIdent (mkIdent (debugPrefix ++ name ident ++ suffix)) (uniqueId ident)


\end{verbatim}

Qualified data types representing some useful types in the transformed program:
{\tt [a], (a,b), Char, [Char], CTree} and {\tt [Ctree]}. Also function for
constructing expressions of the form (a,b) and the name of function 
{\tt clean}.

\begin{verbatim}

> typeCons :: Type
> typeCons = TypeArrow (TypeVariable 0) 
>               (TypeArrow (debugTypeList (TypeVariable 0))  
>                          (debugTypeList (TypeVariable 0)))

> typeTuple :: Int -> Type
> typeTuple n = foldr TypeArrow (debugTypeTuple ts) ts
>   where ts = [TypeVariable i | i <- [0 .. n - 1]]

> debugTypeList :: Type -> Type
> debugTypeList t = TypeConstructor qListId [t]

> debugTypePair :: Type -> Type -> Type
> debugTypePair a b = TypeConstructor qPairId [a,b]

> debugTypeTuple :: [Type] -> Type
> debugTypeTuple ts = TypeConstructor (qTupleId (length ts)) ts

> debugTypeChar,debugTypeString:: Type
> debugTypeChar   = TypeConstructor qCharId []
> debugTypeString = debugTypeList debugTypeChar


> debugTypeCTree,debugTypeLCTree,debugTypeCleanTree,debugTypeLCleanTree:: Type
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
> debugClean  = debugQualPreludeName "clean"

> debugPerformIO :: QualIdent
> debugPerformIO = debugQualPreludeName "performIO"

> debugTry :: QualIdent 
> debugTry  = debugQualPreludeName "try'"

> debugReturn :: QualIdent
> debugReturn  = debugQualPreludeName "return'"

> debugBind :: QualIdent
> debugBind  = debugQualPreludeName "bind'"

> debugBind_ :: QualIdent
> debugBind_  = debugQualPreludeName "bind_'"

> debugCatch :: QualIdent
> debugCatch  = debugQualPreludeName "catch'"

> debugFixIO :: QualIdent
> debugFixIO  = debugQualPreludeName "fixIO'"

> debugEncapsulate :: QualIdent
> debugEncapsulate  = debugQualPreludeName "encapsulate'"


> dEvalApply :: Expression -> Expression
> dEvalApply = Apply (Function (debugQualPreludeName "dEval") 1)


> void :: Expression
> void = Constructor (debugQualPreludeName "CTreeVoid") 0

> emptyNode :: Expression -> Expression
> emptyNode children =
>   createApply (Constructor (debugQualPreludeName "EmptyCTreeNode") 1)
>               [children]


> debugBuildList :: [Expression] -> Expression
> debugBuildList l = foldr Apply debugNil (map (Apply cons) l)
>   where cons = Constructor qConsId 2


> node :: Expression -> Expression -> Expression -> Expression -> Expression
>      -> Expression
> node name args result number children =
>   createApply (Constructor (debugQualPreludeName "CTreeNode") 5)
>               [name, args, result, number, children]

\end{verbatim}

The newMain is only added if we are in the module main. 
It will start the debugging process.

Its definition depends on the goal's type. If the goal's type is
\texttt{IO}~$t$, the new main function simply executes the transformed
goal under control of the debugger.

\begin{verbatim}


main.main = DebugPrelude.startIODebugging main._debug#main

\end{verbatim}

Otherwise, the goal must be solved using encapsulated search and
navigation then allows picking a wrong solution. In order to make this
work, the transformed goal function must be converted into a form that
is suitable as argument to the encapsulated search primitive
\texttt{try}. Therefore, we use the following definition for the new
main function.

\begin{verbatim}


main.main = DebugPrelude.startDebugging 
                (\(x,ct)-> let (r,ct') = main._debug#main in x=:=r &> ct=:=ct')

\end{verbatim}

We have to introduce an auxiliary function for the lambda in the intermediate code.

\begin{verbatim}

> dAddMain :: Ident -> Module -> Module
> dAddMain goalId (Module m is ds) = Module m is (fMain ++ ds)
>   where (arity,ty) = head [(length lVars,ty) | FunctionDecl f lVars ty _ <- ds, f == debugOldMainId]
>         fMain = if isIO
>                 then newMainIO m goalId arity
>                 else newMain m goalId arity
>         debugOldMainId = qualifyWith m (debugRenameId "" goalId)
>         debugResultType (TypeConstructor _ [ty,_]) = ty
>         isIO =
>           case arity of
>             0 -> isIOType (debugResultType ty)
>             1 -> isIOType ty
>             _ -> False

> newMainIO :: ModuleIdent -> Ident -> Int -> [Decl]
> newMainIO m f n = [fMain]
>       where 
>       fMain = FunctionDecl fId [] fType fBody
>       fId   = qualifyWith m f
>       fType = TypeConstructor qIOId [TypeConstructor qUnitId []]
>       fApp  = if n==0
>               then Function debugOldMainId n
>               else debugBuildPairExp (Function debugOldMainId n) void
>       fBody = Apply (Function debugIOFunctionqId 2) fApp
>       debugOldMainId = qualifyWith m (debugRenameId "" f)

> newMain :: ModuleIdent -> Ident -> Int -> [Decl]
> newMain m f n = [fMain,auxMain]
>       where 
>       fMain = FunctionDecl fId [] fType fBody
>       fId   = qualifyWith m f
>       fType = TypeConstructor qIOId [TypeConstructor qUnitId []]
>       fBody = Apply (Function debugFunctionqId 1) (Function debugAuxMainId 1)
>       fType' = debugTypeMainAux
>       r   = mkIdent "r"
>       ct' = mkIdent "ct'"
>       x   = mkIdent "x"
>       ct   = mkIdent "ct"
>       param  = mkIdent "x_ct"
>       eq1 = createApply equalFunc  [Variable x, Variable r]
>       eq2 = createApply equalFunc  [Variable ct, Variable ct']        
>       equalFunc = Function (qualifyWith preludeMIdent (mkIdent "=:=")) 2
>       seqAndFunc = Function (qualifyWith preludeMIdent (mkIdent "&>")) 2
>       expression =  createApply seqAndFunc [eq1,eq2]
>       alt'     = Alt (ConstructorPattern qPairId [x,ct]) expression
>       caseExpr = Case Flex (Variable param) [alt']
>       alt      = Alt (ConstructorPattern qPairId [r,ct']) caseExpr
>       fApp     = if n == 0
>                  then Function debugOldMainId n
>                  else debugBuildPairExp (Function debugOldMainId n) void
>       fBody'   = Case Rigid  fApp [alt]
>       auxMain = FunctionDecl debugAuxMainId [param] fType' fBody'
>       debugOldMainId = qualifyWith m (debugRenameId "" f)
>       debugAuxMainId = qualifyWith m (debugRenameId "#Aux" f)


\end{verbatim}
Foreign functions cannot be changed by the debugging transformation,
since their implementation is unknown. In order to integrate foreign
functions into the transformed program, the debugging transformation
introduces an auxiliary function for each foreign function that pairs
the result of the foreign function with a suitable computation tree.
For first order foreign functions, e.g., the arithmetic primitives,
that computation tree is simply a void tree.

The situation is different for higher order primitives like
\texttt{try} and foreign functions defined in the \texttt{IO} monad.
These functions can perform arbitrary computations and may invoke user
defined functions. Therefore associating a void tree is not
sufficient. Instead the transformation is using some helper functions
defined in the \texttt{DebugPrelude}, which collect the computation
trees of the subcomputations and return them along with the
computation tree of the transformed function.
\begin{verbatim}

> generateForeign :: ModuleIdent -> QualIdent -> CallConv -> String -> Int
>                 -> Type -> Decl
> generateForeign m qId cc s n fType = 
>       FunctionDecl qId' varsId fType' body
>       where
>       qId'             = changeFunctionqId qId
>       isIO             = isIOType (resultType fType)
>       varsId           = map (mkIdent.("_"++).show) [0..n-1]
>       vars             = map Variable varsId
>       vars'            = init vars
>       fType'           = transformType n  fType
>       bind             = qualifyWith preludeMIdent (mkIdent ">>=")
>       ioDict           = qualifyWith preludeMIdent (mkIdent "_Inst#Prelude.Monad#Prelude.IO")
>       finalApp         = case foreignWrapper cc s of
>                            Just qId'' -> createApply (Function qId'' n) vars
>                            Nothing
>                              | any isFunctType (argumentTypes fType) ->
>                                  error ("generateForeign: unsupported higher order primitive " ++ s)
>                              | otherwise -> createApply (Function qId n) vars
>       finalAppIO       = case foreignWrapper cc s of
>                            Just qId'' -> createApply (Function qId'' n) vars'
>                            Nothing
>                              | any isFunctType (argumentTypes fType) ->
>                                  error ("generateForeign: unsupported higher order primitive " ++ s)
>                              | otherwise ->
>                                  createApply (Function bind 1)
>                                              [Function ioDict 0,
>                                               createApply (Function qId n) vars',
>                                               Function debugReturn 2]
>       body             = if cc==Primitive && s=="unsafePerformIO"
>                          then createApply (Function qId n) vars
>                          else if isIO
>                               then Apply finalAppIO (last vars)
>                               else debugBuildPairExp finalApp void
>       isFunctType ty   = isArrowType ty || isIOType ty

> foreignWrapper :: CallConv -> String -> Maybe QualIdent
> foreignWrapper Primitive s
>   | s=="try"             = Just debugTry
>   | s=="return"          = Just debugReturn
>   | s==">>="             = Just debugBind
>   | s==">>"              = Just debugBind_
>   | s=="catch"           = Just debugCatch
>   | s=="fixIO"           = Just debugFixIO
>   | s=="encapsulate"     = Just debugEncapsulate
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

> generateAuxFuncs :: ModuleIdent -> (QualIdent,SymbolType,Int,Type) -> [Decl]
> generateAuxFuncs m (qId,sType,n,fType) =
>   map (generateAuxFunc m qId sType k fType) [0..k]
>   where k = if sType==IsConstructor then n-1 else n-2 

> generateAuxFunc :: ModuleIdent -> QualIdent -> SymbolType -> Int -> Type
>                 -> Int -> Decl
> generateAuxFunc m qId sType n fType i =
>       FunctionDecl qIdent' varsId fType' exp'
>       where
>       (idModule,ident) = splitQualIdent qId
>       qId'             = changeFunctionqId qId
>       ident'           = idAuxiliarFunction ident i
>       ident''          = idAuxiliarFunction ident (i+1)
>       qIdent'          = qualifyWith m ident'
>       qIdent''         = qualifyWith m ident''
>       varsId           = map (mkIdent.("_"++).show) [0..i]
>       vars             = map Variable varsId
>       fType'           = transformType (i+1)  fType
>       finalApp         = if sType==IsConstructor
>                          then createApply (Constructor qId (i+1)) vars
>                          else createApply (Function qId' (i+2)) vars
>       nextApp          = createApply (Function qIdent'' (i+2)) vars
>       exp'             = if (i==n)
>                          then  debugBuildPairExp finalApp void
>                          else  debugBuildPairExp nextApp void

> idAuxiliarFunction :: Ident -> Int -> Ident
> idAuxiliarFunction ident n = debugRenameId ('#':show n) ident

> extractApply :: Expression -> [Expression] -> (Expression,[Expression])
> extractApply (Apply e1 e2) l = extractApply e1 (e2:l)
> extractApply e1 l =  (e1,l)

                                           
> createApply :: Expression  -> [Expression] -> Expression 
> createApply exp lExp  = foldl Apply exp lExp


\end{verbatim}


The function \texttt{transformType} transforms the type
$\tau_1 \rightarrow \dots \rightarrow \tau_n \rightarrow \tau$
of a function with arity $n$ into
$\tau'_1 \rightarrow \dots \rightarrow \tau'_n \rightarrow (\tau',\texttt{CTree})$.
The arity $n$ is passed as first argument to \texttt{transformType}.

The function \texttt{transformType'} implements the basic
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

> transformType :: Int -> Type -> Type
> transformType 0 fType = debugTypePair (transformType' fType) debugTypeCTree
> transformType _ fType@(TypeArrow ty1 (TypeConstructor tc [ty2,ty3]))
>   | tc == qPairId && ty1 == TypeConstructor qWorldId [] && ty1 == ty3 =
>       transformType' fType
> transformType n (TypeArrow type1 type2) =
>   TypeArrow (transformType' type1) (transformType (n-1) type2)
> transformType _ fType = transformType' fType

> transformType' :: Type -> Type
> transformType' (TypeArrow ty1 (TypeConstructor tc [ty2,ty3]))
>   | tc == qPairId && ty1 == TypeConstructor qWorldId [] && ty1 == ty3 =
>       TypeArrow ty1 (TypeConstructor tc [transformType 0 ty2,ty3])
> transformType' t@(TypeArrow type1 type2) = transformType 1 t
> transformType' (TypeConstructor tc lTypes)
>   | tc == qIOId = TypeConstructor tc [transformType 0 (head lTypes)]
>   | otherwise = TypeConstructor tc (map transformType' lTypes)
> transformType' (TypeVariable v) = TypeVariable v

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

The transformation must add auxiliary functions for all partial applications
of the list constructor and tuple constructors which are used in the module.
These constructors are defined implicitly in every module, therefore we collect
these definitions here.
\begin{verbatim}

> type DebugTypeList = [(QualIdent,SymbolType,Int,Type)]

> typesPredefined :: [Decl] -> DebugTypeList
> typesPredefined ds = nub (foldr typesBody [] ds)

> typesBody :: Decl -> DebugTypeList -> DebugTypeList
> typesBody (DataDecl _ _ _) = id
> typesBody (TypeDecl _ _ _) = id
> typesBody (FunctionDecl _ _ _ e) = typesExpr e
> typesBody (ForeignDecl _ _ _ _) = id

> typesExpr :: Expression -> DebugTypeList -> DebugTypeList
> typesExpr (Literal _) env = env
> typesExpr (Variable _) env = env
> typesExpr (Function _ _) env = env
> typesExpr (Constructor qId n) env =
>   if idModule == Nothing && n > 0 then env' else env
>   where (idModule,ident) = splitQualIdent qId
>         env' = (qId,IsConstructor,n,debugTypePredef ident n) : env
> typesExpr (Apply e1 e2) env = typesExpr e1 (typesExpr e2 env)
> typesExpr (Case _ e alts) env = typesExpr e (foldr typesAlt env alts)
>   where typesAlt (Alt _ e) = typesExpr e
> typesExpr (Or e1 e2) env = typesExpr e1 (typesExpr e2 env)
> typesExpr (Exist _ e) env = typesExpr e env
> typesExpr (Let (Binding _ e1) e2) env = typesExpr e1 (typesExpr e2 env)
> typesExpr (Letrec binds e) env = foldr typesBinding (typesExpr e env) binds
>   where typesBinding (Binding _ e) = typesExpr e

> debugTypePredef :: Ident -> Int -> Type
> debugTypePredef ident n
>   | ident == consId && n == 2 = typeCons
>   | isTupleId ident = typeTuple n
>   | otherwise = error ("debugTypePredef: " ++ show ident ++ "/" ++ show n)

\end{verbatim}

The transformation of user defined functions is performed in two
phases.

\begin{verbatim}

> debugFunction :: ModuleIdent -> (QualIdent -> Bool) -> QualIdent -> [Ident]
>               -> Type -> Expression -> Decl
> debugFunction m trusted f vs ty e = FunctionDecl f' vs ty' e'
>   where f' = changeFunctionqId f
>         ty' = transformType (length vs) ty
>         e' = debugSecondPhase f (trusted f) vs ty' (debugFirstPhase m e)

\end{verbatim}

The first phase of the transformation process changes the names of all
function and partial constructor applications.

\begin{verbatim}

> debugFirstPhase :: ModuleIdent -> Expression -> Expression
> debugFirstPhase m e = firstPhase m 0 e

> class FirstPhase a where
>   firstPhase :: ModuleIdent -> Int -> a -> a

> instance FirstPhase a => FirstPhase [a] where
>   firstPhase m d = map (firstPhase m d)

> instance FirstPhase Expression where
>   firstPhase _ _ (Literal l) = Literal l
>   firstPhase _ _ (Variable v) = Variable v
>   firstPhase m d (Function f n)
>     | isQSelectorId f = Function f n
>     | otherwise       = firstPhaseQual m n d f True
>   firstPhase m d (Constructor c n) = firstPhaseQual m n d c False
>   firstPhase m d (Apply e1 e2) =
>     Apply (firstPhase m (d+1) e1) (firstPhase m 0 e2)
>   firstPhase m d (Case eval expr lAlts) =
>     Case eval (firstPhase m 0 expr) (firstPhase m d lAlts)
>   firstPhase m d (Or e1 e2) = Or (firstPhase m d e1) (firstPhase m d e2)
>   firstPhase m d (Exist ident e) = Exist ident (firstPhase m d e)
>   firstPhase m d (Let binding e) =
>     Let (firstPhase m 0 binding) (firstPhase m d e)
>   firstPhase m d (Letrec lbind e) =
>     Letrec (firstPhase m 0 lbind) (firstPhase m d e)

> instance FirstPhase Alt where
>   firstPhase m d (Alt term expr) = Alt term (firstPhase m d expr)

> instance FirstPhase Binding where
>   firstPhase m d (Binding ident expr) = Binding ident (firstPhase m d expr)

> firstPhaseQual :: ModuleIdent -> Int -> Int -> QualIdent -> Bool -> Expression
> firstPhaseQual m arity nArgs qIdent isFunction
>   | mustBeChanged = Function qIdent' (nArgs+1)
>   | isFunction    = Function qIdent'' arity
>   | otherwise     = Constructor qIdent arity
>   where mustBeChanged = if isFunction then nArgs < arity-1 else nArgs < arity
>         (idModule,ident) = splitQualIdent qIdent
>         idModule' = maybe m id idModule
>         qIdent'   = qualifyWith idModule' (idAuxiliarFunction ident nArgs)
>         qIdent''  = qualifyWith idModule' (debugRenameId "" ident)

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

A special cases handles $\eta$-expanded functions with result type
\texttt{IO}~$t$. According to the special transformation rule that
applies to the \texttt{IO} type (see notes on \texttt{transformType}),
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
> newLocalDeclarations f trust vs e = fst (newBindings createNode e 0 [])
>   where createNode = if trust then createEmptyNode else createTree f vs

> newLocalDeclarationsEtaIO :: QualIdent -> Bool -> [Ident] -> Expression
>                           -> Expression
> newLocalDeclarationsEtaIO f trust vs e =
>   etaExpandIO (newLocalDeclarations f trust (init vs) e') v
>   where (e',v) = etaReduceIO e

> etaExpandIO :: Expression -> Expression -> Expression
> etaExpandIO (Case rf e as) = Case rf e . zipWith etaExpandIOAlt as . repeat
>   where etaExpandIOAlt (Alt t e) = Alt t . etaExpandIO e
> etaExpandIO (Exist v e)    = Exist v . etaExpandIO e
> etaExpandIO (Let d e)      = Let d . etaExpandIO e
> etaExpandIO (Letrec ds e)  = Letrec ds . etaExpandIO e
> etaExpandIO e              = Apply (Apply (Function debugPerformIO 2) e)

> etaReduceIO :: Expression -> (Expression,Expression)
> etaReduceIO (Apply e1 e2) = (e1, e2)
> etaReduceIO (Case rf e1 [Alt t e2]) = (Case rf e1 [Alt t e2'], v)
>                                               where (e2', v) = etaReduceIO e2
> etaReduceIO (Exist v e)   = (Exist v e', v')  where (e', v') = etaReduceIO e
> etaReduceIO (Let d e)     = (Let d e', v)     where (e', v) = etaReduceIO e
> etaReduceIO (Letrec ds e) = (Letrec ds e', v) where (e', v) = etaReduceIO e
> etaReduceIO e = error ("etaReduceIO " ++ showsPrec 11 e "")


\end{verbatim}

This type represents the result of the next set of functions. The
first part is a list with the new computation trees introduced,
prepared for function \texttt{clean}, the second is a context for the
transformed expression with the new local definitions (bindings)
introduced. The third component is the transformed expression itself
(without the new local definitions).

\begin{verbatim}

> type SecondPhaseResult = ([Expression],Context,Expression,Int)
> type Context = Expression -> Expression

\end{verbatim}

The next function changes an expression \texttt{e} into
\texttt{let aux$N$ = e in } \texttt{let result$N$ = fst e in }
\texttt{let tree$N$ = snd e in} \texttt{Variable result$N$},
where $N$ represents a number used to ensure distinct names of
variables. Actually this information is returned in the following,
more convenient format:
\texttt{(Trees++[cleanTree], lets, Variable resultId)}, where
\texttt{cleanTree} is \texttt{(dVal result$N$, tree$N$)} and
\texttt{lets} is the context for the transformed expression, i.e., the
local declarations of \texttt{aux$N$}, \texttt{result$N$}, and
\texttt{tree$N$}.

\begin{verbatim}

> decomposeExp :: [Expression] -> Int -> Expression -> SecondPhaseResult
>
> decomposeExp lTrees n exp = (lTrees++[cleanTree],lets,Variable resultId,n+1)
>   where treeId    = newIdName n "tree"
>         resultId  = newIdName n "result"
>         aux       = newIdName n "Aux"
>         auxResult = Apply (Function fst 1) (Variable aux)
>         auxTree   = Apply (Function snd 1) (Variable aux)
>         fst       = qualifyWith preludeMIdent (mkIdent "fst")
>         snd       = qualifyWith preludeMIdent (mkIdent "snd")
>         lets      = Let (Binding aux exp) .
>                     Let (Binding resultId auxResult) .
>                     Let (Binding treeId auxTree)
>         cleanTree = retrieveCleanTree (resultId,treeId)



> newBindings :: (Ident -> [Expression] -> Expression) -> Expression -> Int
>             -> [Expression] -> (Expression,Int)
> newBindings createNode exp n lTrees =
>   if isCaseOrExp then (lets exp2,n2) else (letExp,n2+1)
>   where isCaseOrExp = caseOr exp
>         (lTrees2,lets,exp2,n2) =
>           extractBindings isCaseOrExp createNode exp n lTrees
>         treeId   = newIdName n2 "tree"
>         resultId = newIdName n2 "result"
>         cTree    = createNode resultId lTrees2
>         rhs      = debugBuildPairExp (Variable resultId) (Variable treeId)
>         bindingR = Binding resultId exp2
>         bindingT = Binding treeId cTree
>         letExp   = (lets . Let bindingR . Let  bindingT) rhs


> extractBindings :: Bool -> (Ident -> [Expression] -> Expression) -> Expression
>                 -> Int -> [Expression] -> SecondPhaseResult
>
> extractBindings _ _ e@(Function f a) n lTrees
>   | a > 0 = (lTrees,id,e,n)
>   | otherwise = decomposeExp lTrees n e

> extractBindings isMainExp createNode (Case eval exp lAlt) n lTrees
>   | isMainExp = ([],lets,Case eval e1 lAlt',n2)
>   | otherwise = decomposeExp [] n2 (lets (Case eval e1 lAlt'))
>   where (lTrees1,lets,e1,n1) =
>           extractBindings False createEmptyNode exp n lTrees
>         (lAlt',n2) = newBindingsAlts createNode lAlt n1 lTrees1

> extractBindings isMainExp createNode (Or e1 e2) n lTrees
>   | isMainExp = ([],id,Or e1' e2',n2)
>   | otherwise = decomposeExp [] n2 (Or e1' e2')
>   where (e1',n1) = newBindings createNode e1 n lTrees
>         (e2',n2) = newBindings createNode e2 n1 lTrees

> extractBindings isMainExp createNode (Exist id exp) n lTrees =
>   (lTrees',Exist id . lets',exp',n')
>   where (lTrees',lets',exp',n') =
>           extractBindings isMainExp createNode exp n lTrees

> extractBindings isMainExp createNode (Let binding e) n lTrees =
>   (lTrees2,lets1 . lets2,e',n2)
>   where (lTrees1,lets1,n1) = extractBindingsBinding binding n
>         (lTrees2,lets2,e',n2) =
>           extractBindings isMainExp createNode e n1 (lTrees++lTrees1)

> extractBindings isMainExp createNode (Letrec lbinding e) n lTrees =
>   (lTrees2,letrecBindings lets1 . lets2,e',n2)
>   where (lTrees1,lets1,n1) = extractBindingsLBindings lbinding n
>         (lTrees2,lets2,e',n2) =
>           extractBindings isMainExp createNode e n1 (lTrees++lTrees1)
>
> extractBindings isMainExp createNode e@(Apply _ _) n lTrees =
>   (lTrees++lTrees1++lTrees2,letsargs . letse,e1,n2)
>   where (f,args) = extractApply e []
>         (lTrees1,letsargs,args1,n1) = extractBindingsList args n
>         (lTrees2,letse,e1,n2) = extractBindingsApply f args1 n1
>
> extractBindings _ _ exp n lTrees = (lTrees,id,exp,n)


> extractBindingsApply :: Expression -> [Expression] -> Int -> SecondPhaseResult

> extractBindingsApply e@(Constructor _ _) args n = ([],id,createApply e args,n)

> extractBindingsApply f@(Function qId arity) args n
>   | length args == arity-1 = ([],id,partialApp,n)
>   | isQSelectorId qId = extractBindingsApply app extraArgs n
>   | otherwise = (lTrees1++lTrees2,lets1 . lets2,e,n2)
>   where (nArgs,extraArgs) = splitAt arity args
>         app = createApply f nArgs
>         partialApp = createApply f args --05-12-2001
>         (lTrees1,lets1,v,n1) = decomposeExp [] n app
>         (lTrees2,lets2,e,n2) = extractBindingsApply v extraArgs n1

> extractBindingsApply f [] n = ([],id,f,n)
> 
> extractBindingsApply f (e:es) n = (t++t',lets . lets',e',n2)
>   where app = createApply f [e]
>         (t,lets,v,n1) = decomposeExp [] n app
>         (t',lets',e',n2) = extractBindingsApply v es n1


> extractBindingsList :: [Expression] -> Int
>                     -> ([Expression],Context,[Expression],Int)
> extractBindingsList [] n = ([],id,[],n)
> extractBindingsList (x:xs) n = (lTrees1++lTrees2, lets1 . lets2, x':xs', n2)
>   where (lTrees1,lets1,x',n1) = extractBindings False createEmptyNode x n []
>         (lTrees2,lets2,xs',n2) = extractBindingsList xs n1


> extractBindingsBinding :: Binding -> Int -> ([Expression],Context,Int)
> extractBindingsBinding (Binding vId e) n = (lTrees,lBinding,n')
>   where (lTrees,lets,e1,n') = extractBindings False createEmptyNode e n []
>         lBinding = lets . Let (Binding vId e1)


> extractBindingsLBindings :: [Binding] -> Int -> ([Expression],Context,Int)
> extractBindingsLBindings [] n = ([],id,n)
> extractBindingsLBindings (x:xs) n = (lTrees1++lTrees2,letsX . letsXs,n2)
>   where (lTrees1,letsX,n1) = extractBindingsBinding x n
>         (lTrees2,letsXs,n2) = extractBindingsLBindings xs n1


> newBindingsAlts :: (Ident -> [Expression] -> Expression) -> [Alt] -> Int
>                 -> [Expression] -> ([Alt],Int)
> newBindingsAlts _ [] n _ = ([],n)
> newBindingsAlts createNode (Alt const e:xs) n lTrees = (Alt const e':xs',n2)
>   where (e',n1) = newBindings createNode e n lTrees
>         (xs',n2) = newBindingsAlts createNode xs n1 lTrees


> caseOr :: Expression -> Bool
> caseOr (Literal _) = False
> caseOr (Variable _) = False
> caseOr (Function _ _) = False
> caseOr (Constructor _ _) = False
> caseOr (Apply e1 _) = caseOr e1
> caseOr (Case _ _ _) = True
> caseOr (Or _ _) = True
> caseOr (Exist _ exp) = caseOr exp
> caseOr (Let _ exp) = caseOr exp
> caseOr (Letrec _ exp) = caseOr exp

> createTree :: QualIdent ->  [Ident] -> Ident -> [Expression] -> Expression
> createTree qId lVars resultId trees =
>   node fName fParams fResult debugNil clean
>   where (idModule,ident) = splitQualIdent qId
>         fNameCh = maybe "" moduleName idModule ++ "." ++ name ident
>         fName   = debugBuildList (map (Literal . Char) fNameCh)
>         fParams = debugBuildList (map (dEvalApply.Variable) lVars)
>         fResult = (dEvalApply.Variable) resultId
>         clean   = if null trees then debugNil
>                   else Apply (Function debugClean 1) (debugBuildList trees)

> createEmptyNode :: Ident -> [Expression] -> Expression
> createEmptyNode resultId trees = if null trees then void else emptyNode clean
>   where clean = Apply (Function debugClean 1) (debugBuildList trees)

> letrecBindings :: Context -> Context
> letrecBindings bindings =
>   fixLetrecBindings Letrec (bindings (Variable undefined))

> fixLetrecBindings :: ([Binding]->Context) -> Expression -> Context
> fixLetrecBindings bindings (Variable _) = bindings []
> fixLetrecBindings bindings (Exist var exp) =
>   Exist var . fixLetrecBindings bindings exp
> fixLetrecBindings bindings (Let binding exp) =
>   fixLetrecBindings (bindings . (binding:)) exp
> fixLetrecBindings bindings (Letrec lbindings exp) =
>   fixLetrecBindings (bindings . (lbindings++)) exp

\end{verbatim}


Function {\tt retrieveCleanTree} convert a value {\tt SecondPhaseResult} 
of the form {(res,tree),exp)} representing
a  new local let, into an element of the list of trees of the form
{\tt (dEval res,tree)}.

\begin{verbatim}

> retrieveCleanTree :: (Ident,Ident) -> Expression
> retrieveCleanTree (id1,id2) = debugBuildPairExp id1' id2'
>       where
>        id1' = dEvalApply (Variable id1 )
>        id2' = Variable id2


\end{verbatim}

\begin{verbatim}

> changeFunctionqId :: QualIdent -> QualIdent
> changeFunctionqId qId = qId'
>       where
>       (idModule,ident) = splitQualIdent qId
>       ident'    = debugRenameId "" ident
>       qId'      = maybe qId (flip qualifyWith ident') idModule

\end{verbatim}

