% -*- LaTeX -*-
% $Id: Modules.lhs 3136 2013-05-12 15:53:27Z wlux $
%
% Copyright (c) 1999-2013, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Modules.lhs}
\section{Modules}
This module controls the compilation of modules.
\begin{verbatim}

> module Modules(compileModule) where
> import CaseCheck
> import Combined
> import Common
> import Curry
> import CurryParser
> import CurryUtils
> import Deriving
> import Error
> import ExportSyntaxCheck
> import Exports
> import IdentInfo
> import ImportSyntaxCheck
> import InstCheck
> import InstInfo
> import Interfaces
> import KindCheck
> import List
> import Monad
> import Options
> import OverlapCheck
> import Position
> import PrecCheck
> import PrecInfo
> import PredefIdent
> import Qual
> import Renaming
> import ShadowCheck
> import SyntaxCheck
> import Types
> import TypeCheck
> import TypeInfo
> import TypeSyntaxCheck
> import Unlit
> import UnusedCheck
> import Utils
> import ValueInfo

\end{verbatim}
The function \texttt{compileModule} is the main entry point of this
module for compiling a Curry source module. It applies syntax and type
checking to the module and translates the code into one or more C code
files. The module's interface is updated when necessary. Note that the
interface is computed from the environments returned by the front end
but the source code \emph{after} applying the program transformations
(cf.\ Sect.~\ref{sec:exports}).

The compiler automatically loads the Prelude when compiling a module
-- except for the Prelude itself -- by adding an appropriate import
declaration to the module.
\begin{verbatim}

> compileModule :: Options -> FilePath -> ErrorT IO ()
> compileModule opts fn =
>   do
>     (pEnv,tcEnv,iEnv,tyEnv,m) <- loadModule paths dbg cm ws fn
>     let (tcEnv',tyEnv',trEnv,m',dumps) = transModule dbg tr tcEnv tyEnv m
>     liftErr $ mapM_ (doDump opts) dumps
>     let intf = exportInterface m' pEnv tcEnv iEnv tyEnv
>     liftErr $ unless (noInterface opts) (updateInterface fn intf)
>     let (tcEnv'',tyEnv'',trEnv',m'',dumps) =
>           dictTrans tcEnv' iEnv tyEnv' trEnv m'
>     liftErr $ mapM_ (doDump opts) dumps
>     let (il,dumps) = ilTransModule dbg tcEnv'' tyEnv'' trEnv' Nothing m''
>     liftErr $ mapM_ (doDump opts) dumps
>     let (ccode,dumps) = genCodeModule split dbg tcEnv'' il
>     liftErr $ mapM_ (doDump opts) dumps >>
>               writeCode (output opts) fn ccode
>   where paths = importPath opts
>         split = splitCode opts
>         dbg = debug opts
>         tr = if trusted opts then Trust else Suspect
>         cm = caseMode opts
>         ws = warn opts

> loadModule :: [FilePath] -> Bool -> CaseMode -> [Warn] -> FilePath
>            -> ErrorT IO (PEnv,TCEnv,InstEnv,ValueEnv,Module QualType)
> loadModule paths debug caseMode warn fn =
>   do
>     Module m es is ds <- liftErr (readFile fn) >>= okM . parseModule fn
>     let is' = importPrelude debug fn m is
>     mEnv <- loadInterfaces paths m (modules is')
>     (tEnv,vEnv,m') <- okM $ checkModuleSyntax mEnv (Module m es is' ds)
>     liftErr $ mapM_ putErrLn $ warnModuleSyntax caseMode warn mEnv m'
>     (pEnv,tcEnv,iEnv,tyEnv,m'') <- okM $ checkModule mEnv tEnv vEnv m'
>     liftErr $ mapM_ putErrLn $ warnModule warn tyEnv m''
>     return (pEnv,tcEnv,iEnv,tyEnv,m'')
>   where modules is = [P p m | ImportDecl p m _ _ _ <- is]

> parseModule :: FilePath -> String -> Error (Module ())
> parseModule fn s = unlitLiterate fn s >>= parseSource fn

> checkModuleSyntax :: ModuleEnv -> Module a -> Error (TypeEnv,FunEnv,Module a)
> checkModuleSyntax mEnv (Module m es is ds) =
>   do
>     is' <- importSyntaxCheck mEnv is
>     let (tEnv,iSet,vEnv) = importModuleIdents mEnv is'
>     (tEnv',ds') <- typeSyntaxCheck m tEnv iSet ds
>     (vEnv',ds'') <- syntaxCheck m tEnv' vEnv ds'
>     es' <- checkExports m is' tEnv' vEnv' es
>     return (tEnv',vEnv',Module m (Just es') is' ds'')

> checkModule :: ModuleEnv -> TypeEnv -> FunEnv -> Module ()
>             -> Error (PEnv,TCEnv,InstEnv,ValueEnv,Module QualType)
> checkModule mEnv tEnv vEnv (Module m es is ds) =
>   do
>     let (k1,ds') = rename k0 ds
>     let (pEnv,tcEnv,iEnv,tyEnv) = importModules mEnv is
>     let (pEnv',tcEnv',tyEnv') = qualifyEnv1 mEnv is pEnv tcEnv tyEnv
>     (pEnv'',ds'') <- precCheck m tcEnv' pEnv' (qual1 tEnv vEnv ds')
>     tcEnv'' <- kindCheck m tcEnv' ds''
>     iEnv' <- instCheck m tcEnv'' iEnv ds''
>     (k2,deriv) <- liftM (rename k1) (derive m pEnv'' tcEnv'' iEnv' ds'')
>     (tyEnv'',ds''') <- typeCheck m tcEnv'' iEnv' tyEnv' (ds'' ++ deriv)
>     let (pEnv''',tcEnv''',tyEnv''') =
>           qualifyEnv2 mEnv m pEnv'' tcEnv'' tyEnv''
>     return (pEnv''',tcEnv''',iEnv',tyEnv''',
>             Module m es is (qual2 tEnv vEnv ds'''))

> importSyntaxCheck :: ModuleEnv -> [ImportDecl] -> Error [ImportDecl]
> importSyntaxCheck mEnv ds = mapE checkImportDecl ds
>   where checkImportDecl (ImportDecl p m q asM is) =
>           liftE (ImportDecl p m q asM)
>                 (checkImports (moduleInterface m mEnv) is)

> warnModuleSyntax :: CaseMode -> [Warn] -> ModuleEnv -> Module a -> [String]
> warnModuleSyntax caseMode warn mEnv m =
>   caseCheck caseMode m ++ unusedCheck warn m ++ shadowCheck warn mEnv m

> warnModule :: [Warn] -> ValueEnv -> Module a -> [String]
> warnModule warn tyEnv m = overlapCheck warn tyEnv m

\end{verbatim}
The Prelude is imported implicitly into every module other than the
Prelude. If the module does not import the Prelude explicitly, the
added declaration brings all Prelude entities with qualified and
unqualified names into scope. Otherwise, only the identifiers of the
unit, list, and tuple types are imported. Furthermore, the module
\texttt{DebugPrelude} is imported into every module when it is
compiled for debugging. However, none of its entities are brought into
scope because the debugging transformation is applied to the
intermediate language.
\begin{verbatim}

> importPrelude :: Bool -> FilePath -> ModuleIdent
>               -> [ImportDecl] -> [ImportDecl]
> importPrelude debug fn m is =
>   imp True preludeMIdent (preludeMIdent `notElem` ms) ++
>   imp debug debugPreludeMIdent False ++ is
>   where p = first fn
>         ms = [m | ImportDecl _ m _ _ _ <- is]
>         imp cond m' all = [importDecl p m' all | cond && m /= m']

> importDecl :: Position -> ModuleIdent -> Bool -> ImportDecl
> importDecl p m all =
>   ImportDecl p m False Nothing
>              (if all then Nothing else Just (Importing p []))

\end{verbatim}
Literate source files use the extension \texttt{".lcurry"}.
\begin{verbatim}

> unlitLiterate :: FilePath -> String -> Error String
> unlitLiterate fn s
>   | not (isLiterateSource fn) = return s
>   | null es = return s'
>   | otherwise = fail es
>   where (es,s') = unlit fn s

> isLiterateSource :: FilePath -> Bool
> isLiterateSource fn = ".lcurry" `isSuffixOf` fn

\end{verbatim}
