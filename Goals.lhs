% -*- LaTeX -*-
% $Id: Goals.lhs 2800 2009-04-26 16:54:22Z wlux $
%
% Copyright (c) 1999-2009, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Goals.lhs}
\section{Goals}\label{sec:goals}
This module controls the compilation of goals.
\begin{verbatim}

> module Goals(compileGoal,typeGoal) where
> import CaseCheck
> import Combined
> import Common
> import Curry
> import CurryParser
> import CurryUtils
> import Error
> import IdentInfo
> import InstInfo
> import Interfaces
> import IO
> import KindCheck
> import List
> import Options
> import OverlapCheck
> import Position
> import PrecCheck
> import PrecInfo
> import PredefIdent
> import PredefTypes
> import Pretty
> import Qual
> import Renaming
> import ShadowCheck
> import SyntaxCheck
> import Types
> import TypeCheck
> import TypeInfo
> import TypeSyntaxCheck
> import TypeTrans
> import Typing
> import UnusedCheck
> import Utils
> import ValueInfo

\end{verbatim}
A goal is compiled with respect to the interface of a given module. If
no module is specified, the Curry Prelude is used. All entities
exported from the main module and the Prelude are in scope with their
unqualified names. In addition, the entities exported from all loaded
interfaces are in scope with their qualified names.
\begin{verbatim}

> data Task = EvalGoal | TypeGoal deriving Eq

> compileGoal :: Options -> Maybe String -> [FilePath] -> ErrorT IO ()
> compileGoal opts g fns =
>   do
>     (tcEnv,iEnv,tyEnv,_,g') <- loadGoal EvalGoal paths dbg cm ws m g fns
>     let (vs,m',tyEnv') = goalModule dbg tyEnv m mainId g'
>     let (tcEnv',tyEnv'',trEnv,m'',dumps) = transModule dbg tr tcEnv tyEnv' m'
>     liftErr $ mapM_ (doDump opts) dumps
>     let (tcEnv'',tyEnv''',m''',dumps) = dictTrans tcEnv' iEnv tyEnv'' m''
>     liftErr $ mapM_ (doDump opts) dumps
>     let (il,dumps) =
>           ilTransModule dbg tcEnv'' tyEnv''' trEnv (Just mainId) m'''
>     liftErr $ mapM_ (doDump opts) dumps
>     let (ccode,dumps) = genCodeGoal tcEnv'' (qualifyWith m mainId) vs il
>     liftErr $ mapM_ (doDump opts) dumps >>
>               writeGoalCode (output opts) ccode
>   where m = mkMIdent []
>         paths = importPath opts
>         dbg = debug opts
>         tr = if trusted opts then Trust else Suspect
>         cm = caseMode opts
>         ws = warn opts

> typeGoal :: Options -> String -> [FilePath] -> ErrorT IO ()
> typeGoal opts g fns =
>   do
>     (tcEnv,_,_,cx,Goal _ e _) <-
>       loadGoal TypeGoal paths False cm ws (mkMIdent []) (Just g) fns
>     liftErr $ maybe putStr writeFile (output opts)
>             $ showLn (ppQualType tcEnv (QualType cx (typeOf e)))
>   where paths = importPath opts
>         cm = caseMode opts
>         ws = warn opts

> loadGoal :: Task -> [FilePath] -> Bool -> CaseMode -> [Warn]
>          -> ModuleIdent -> Maybe String -> [FilePath]
>          -> ErrorT IO (TCEnv,InstEnv,ValueEnv,Context,Goal Type)
> loadGoal task paths debug caseMode warn m g fns =
>   do
>     (mEnv,ms) <- loadGoalModules paths debug fns
>     (tEnv,vEnv,g') <-
>       okM $ maybe (return (mainGoal (last ms))) parseGoal g >>=
>             checkGoalSyntax mEnv ms
>     liftErr $ mapM_ putErrLn $ warnGoalSyntax caseMode warn m g'
>     (tcEnv,iEnv,tyEnv,cx,g'') <-
>       okM $ checkGoal task mEnv m ms tEnv vEnv g'
>     liftErr $ mapM_ putErrLn $ warnGoal warn tyEnv g''
>     return (tcEnv,iEnv,tyEnv,cx,g'')
>   where mainGoal m = Goal (first "") (Variable () (qualifyWith m mainId)) []

> loadGoalModules :: [FilePath] -> Bool -> [FilePath]
>                 -> ErrorT IO (ModuleEnv,[ModuleIdent])
> loadGoalModules paths debug fns =
>   do
>     (mEnv,ms') <- loadGoalInterfaces paths ms fns
>     return (mEnv,preludeMIdent : if null fns then [] else [last ms'])
>   where ms = map (P (first "")) (preludeMIdent : [debugPreludeMIdent | debug])

> checkGoalSyntax :: ModuleEnv -> [ModuleIdent] -> Goal a
>                 -> Error (TypeEnv,FunEnv,Goal a)
> checkGoalSyntax mEnv ms g =
>   do
>     g' <- typeSyntaxCheckGoal tEnv g >>= syntaxCheckGoal vEnv
>     return (tEnv,vEnv,g')
>   where (tEnv,vEnv) = importInterfaceIdents mEnv ms

> checkGoal :: Task -> ModuleEnv -> ModuleIdent -> [ModuleIdent]
>           -> TypeEnv -> FunEnv -> Goal a
>           -> Error (TCEnv,InstEnv,ValueEnv,Context,Goal Type)
> checkGoal task mEnv m ms tEnv vEnv g =
>   do
>     let (k1,g') = renameGoal k0 g
>     let (pEnv,tcEnv,iEnv,tyEnv) = importInterfaces mEnv ms
>     let (pEnv',tcEnv',tyEnv') =
>           qualifyEnv1 mEnv (map importModule ms) pEnv tcEnv tyEnv
>     g'' <- precCheckGoal m pEnv' (qual1 tEnv vEnv g')
>     (tyEnv'',cx,g''') <-
>       kindCheckGoal tcEnv' g'' >>
>       typeCheckGoal (task == EvalGoal) m tcEnv' iEnv tyEnv' g''
>     let (_,tcEnv'',tyEnv''') = qualifyGoalEnv task mEnv m pEnv' tcEnv' tyEnv''
>     return (tcEnv'',iEnv,tyEnv''',cx,qualifyGoal task tEnv vEnv g''')
>   where importModule m = ImportDecl (first "") m False Nothing Nothing

> qualifyGoalEnv :: Task -> ModuleEnv -> ModuleIdent
>                -> PEnv -> TCEnv -> ValueEnv -> (PEnv,TCEnv,ValueEnv)
> qualifyGoalEnv EvalGoal mEnv m pEnv tcEnv tyEnv =
>   qualifyEnv2 mEnv m pEnv tcEnv tyEnv
> qualifyGoalEnv TypeGoal _ _ pEnv tcEnv tyEnv = (pEnv,tcEnv,tyEnv)

> qualifyGoal :: Task -> TypeEnv -> FunEnv -> Goal a -> Goal a
> qualifyGoal EvalGoal tEnv vEnv = qual2 tEnv vEnv
> qualifyGoal TypeGoal _ _ = id

> warnGoalSyntax :: CaseMode -> [Warn] -> ModuleIdent -> Goal a -> [String]
> warnGoalSyntax caseMode warn m g =
>   caseCheckGoal caseMode g ++ unusedCheckGoal warn m g ++
>   shadowCheckGoal warn g

> warnGoal :: [Warn] -> ValueEnv -> Goal a -> [String]
> warnGoal warn tyEnv g = overlapCheckGoal warn tyEnv g

\end{verbatim}
When syntax and type checking succeed goals are compiled by converting
them into a module containing just a single function declaration.
Goals with type \texttt{IO \_} are executed directly by the runtime
system. All other goals are evaluated under control of an interactive
top-level, which displays the solutions of the goal and in particular
the bindings of its free variables. For this reason, the free
variables declared in the \texttt{where} clause of a goal are
translated into free variables of the goal. In addition, the goal is
transformed into a first order expression by performing a unification
with another variable. Thus, a goal
\begin{quote}
 \emph{expr}
 \texttt{where} $v_1$,\dots,$v_n$ \texttt{free}; \emph{decls}
\end{quote}
where no free variable declarations occur in \emph{decls} is
translated into the function
\begin{quote}
  \emph{f} $v_1$ \dots{} $v_n$ $v_{n+1}$ \texttt{=}
    $v_{n+1}$ \texttt{=:=} \emph{expr}
    \texttt{where} \emph{decls}
\end{quote}
where $v_{n+1}$ is a fresh variable. No variables are lifted at
present when generating code for the declarative debugger, since the
debugger evaluates the goal within an encapsulated search and we
cannot pass functions with arbitrary arity to the encapsulated search
primitive. In addition, the debugger currently lacks support for
showing the bindings of the goal's free variables.
\begin{verbatim}

> goalModule :: Bool -> ValueEnv -> ModuleIdent -> Ident -> Goal Type
>            -> (Maybe [Ident],Module Type,ValueEnv)
> goalModule debug tyEnv m g (Goal p e ds)
>   | isIO ty =
>       (Nothing,
>        mkModule m p g [] (mkLet ds e),
>        bindFun m g 0 (polyType ty) tyEnv)
>   | otherwise =
>       (if debug then Nothing else Just vs,
>        mkModule m p g (zip tys vs ++ [(ty,v)])
>                 (apply (prelUnif ty) [mkVar ty v,e']),
>        bindFun m v 0 (monoType ty) (bindFun m g n (polyType ty') tyEnv))
>   where ty = typeOf e
>         v = anonId
>         (vs,e') = liftGoalVars debug (mkLet ds e)
>         tys = [rawType (varType v tyEnv) | v <- vs]
>         ty' = foldr TypeArrow (TypeArrow ty successType) tys
>         n = length vs + 1
>         isIO (TypeApply (TypeConstructor tc) _) = tc == qIOId
>         isIO _ = False

> mkModule :: ModuleIdent -> Position -> Ident -> [(a,Ident)] -> Expression a
>          -> Module a
> mkModule m p g vs e =
>    Module m Nothing []
>           [BlockDecl (funDecl p g (map (uncurry VariablePattern) vs) e)]

> liftGoalVars :: Bool -> Expression a -> ([Ident],Expression a)
> liftGoalVars debug (Let ds e)
>   | not debug = (concat [vs | FreeDecl _ vs <- vds],mkLet ds' e)
>   where (vds,ds') = partition isFreeDecl ds
> liftGoalVars _ e = ([],e)

> prelUnif :: Type -> Expression Type
> prelUnif ty =
>   Variable (foldr TypeArrow successType [ty,ty])
>            (qualifyWith preludeMIdent (mkIdent "=:="))

\end{verbatim}
Auxiliary functions. Unfortunately, hbc's \texttt{IO} module lacks a
definition of \texttt{hPutStrLn}.
\begin{verbatim}

> putErr :: String -> IO ()
> putErr = hPutStr stderr

> putErrLn :: String -> IO ()
> putErrLn s = putErr (unlines [s])

\end{verbatim}