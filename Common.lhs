% -*- LaTeX -*-
% $Id: Common.lhs 2971 2010-07-01 09:44:53Z wlux $
%
% Copyright (c) 1999-2010, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Common.lhs}
\section{Common}
This module contains the common code used for compiling modules as
well as goals.
\begin{verbatim}

> module Common(transModule, dictTrans, ilTransModule, genCodeModule,
>               genCodeGoal, writeCode, writeGoalCode, doDump) where
> import Base
> import qualified Cam
> import qualified CamPP
> import CaseMatch
> import CCode(CFile,mergeCFile)
> import CGen
> import qualified CPretty
> import Curry
> import CurryPP(ppModule,ppIdent)
> import Desugar
> import DictTrans
> import DTransform
> import Env
> import qualified IL
> import ILCompile
> import ILLift
> import qualified ILPP
> import ILTrans
> import InstInfo
> import LazyPatterns
> import Lift
> import List
> import Maybe
> import Monad
> import Newtype
> import Options
> import PathUtils
> import PatternBind
> import Pretty
> import Records
> import Simplify
> import TopEnv
> import Trust
> import TrustInfo
> import Types
> import TypeInfo
> import TypeTrans
> import Utils
> import ValueInfo

\end{verbatim}
The first transformation phase prepares the code for being translated
into the intermediate language. The transformation stops after
simplifying the code and naming lambda abstractions in order to
eventually update the module's interface.
\begin{verbatim}

> transModule :: Bool -> Trust -> TCEnv -> ValueEnv -> Module QualType
>             -> (TCEnv,ValueEnv,TrustEnv,Module QualType,[(Dump,Doc)])
> transModule debug tr tcEnv tyEnv m = (tcEnv',tyEnv''',trEnv,pbu,dumps)
>   where trEnv = if debug then trustEnv tr m else emptyEnv
>         desugared = desugar m
>         unlabeled = unlabel tcEnv tyEnv desugared
>         (tcEnv',tyEnv',nonewtype) = transNewtype tcEnv tyEnv unlabeled
>         nolazy = unlazy nonewtype
>         flatCase = caseMatch tcEnv' nolazy
>         (tyEnv'',simplified) = simplify tcEnv' tyEnv' trEnv flatCase
>         (tyEnv''',pbu) = pbTrans tyEnv'' simplified
>         dumps =
>           [(DumpRenamed,ppModule m),
>            (DumpTypes,ppTypes tcEnv (localBindings tyEnv)),
>            (DumpDesugared,ppModule desugared),
>            (DumpUnlabeled,ppModule unlabeled),
>            (DumpNewtype,ppModule nonewtype),
>            (DumpUnlazy,ppModule nolazy),
>            (DumpFlatCase,ppModule flatCase),
>            (DumpSimplified,ppModule simplified),
>            (DumpPBU,ppModule pbu)]

\end{verbatim}
After creating the module's interface, the compiler introduces
explicit dictionary arguments for overloaded functions and methods.
\begin{verbatim}

> dictTrans :: TCEnv -> InstEnv -> ValueEnv -> Module QualType
>           -> (TCEnv,ValueEnv,Module Type,[(Dump,Doc)])
> dictTrans tcEnv iEnv tyEnv m = (tcEnv',tyEnv',spec,dumps)
>   where (tcEnv',tyEnv',dict) = dictTransModule tcEnv iEnv tyEnv m
>         spec = dictSpecializeModule tcEnv' iEnv dict
>         dumps =
>           [(DumpDict,ppModule dict),
>            (DumpSpecialize,ppModule spec)]

\end{verbatim}
The next transformation phase translates the code into the
intermediate language and eventually applies the debugging
transformation.
\begin{verbatim}

> ilTransModule :: Bool -> TCEnv -> ValueEnv -> TrustEnv -> Maybe Ident
>               -> Module Type -> (IL.Module,[(Dump,Doc)])
> ilTransModule debug tcEnv tyEnv trEnv g m = (ilDbg,dumps)
>   where (tyEnv',trEnv',lifted) = lift tyEnv trEnv m
>         il = ilTrans tcEnv tyEnv' lifted
>         ilDbg
>           | debug =
>               debugAddMain (dTransform (trustedFun trEnv' . unqualify) il)
>           | otherwise = il
>         dumps =
>           [(DumpLifted,ppModule lifted),
>            (DumpIL,ILPP.ppModule il)] ++
>           [(DumpTransformed,ILPP.ppModule ilDbg) | debug]
>         debugAddMain = maybe id dAddMain g

\end{verbatim}
The final transformation phases translate the intermediate language
code into abstract machine code and then generate C code. If a module
is compiled with the \texttt{--split-code} option, the code is split
along the split pragmas inserted implicitly or explicitly into source
code.

If the module in addition is compiled with the debugging
transformation, the compiler strips all data and top level foreign
function declarations from the code. This is a workaround to prevent
name conflicts between the untransformed and transformed code of the
standard library, which could otherwise occur for programs compiled
for debugging because they are linked with the transformed standard
library \emph{and} the untransformed library. The latter is needed by
the small top level program that controls the debugger at runtime.
\begin{verbatim}

> genCodeModule :: Bool -> Bool -> TCEnv -> IL.Module
>               -> (Either CFile [CFile],[(Dump,Doc)])
> genCodeModule False _ tcEnv il = (Left ccode,dumps)
>   where (ccode,dumps) = genCode (dataTypes tcEnv) il
> genCodeModule True debug tcEnv il = (Right ccode,concat (transpose dumps))
>   where (ccode,dumps) = unzip $
>           map (genCode (dataTypes tcEnv) . cleanDebug debug) (splitModule il)

> genCodeGoal :: TCEnv -> QualIdent -> Maybe [Ident] -> IL.Module
>             -> (CFile,[(Dump,Doc)])
> genCodeGoal tcEnv qGoalId vs il = (mergeCFile ccode ccode',dumps)
>   where (ccode,dumps) = genCode (dataTypes tcEnv) il
>         ccode' = genMain (fun qGoalId) (fmap (map name) vs)

> genCode :: [(Cam.Name,[Cam.Name])] -> IL.Module -> (CFile,[(Dump,Doc)])
> genCode ts il = (ccode,dumps)
>   where ilNormal = liftProg il
>         cam = camCompile ilNormal
>         ccode = genModule ts cam
>         dumps =
>           [(DumpNormalized,ILPP.ppModule ilNormal),
>            (DumpCam,CamPP.ppModule cam)]

> splitModule :: IL.Module -> [IL.Module]
> splitModule (IL.Module m is ds) =
>   map (IL.Module m is)
>       (filter (any isCodeDecl) (wordsBy (IL.SplitAnnot ==) ds))
>   where isCodeDecl (IL.DataDecl _ _ cs) = not (null cs)
>         isCodeDecl (IL.TypeDecl _ _ _) = False
>         isCodeDecl (IL.FunctionDecl _ _ _ _) = True
>         isCodeDecl (IL.ForeignDecl _ _ _ _) = True

> cleanDebug :: Bool -> IL.Module -> IL.Module
> cleanDebug True (IL.Module m is ds) = IL.Module m is (filter isUnique ds)
>   where isUnique (IL.DataDecl _ _ _) = False
>         isUnique (IL.TypeDecl _ _ _) = True
>         isUnique (IL.FunctionDecl _ _ _ _) = True
>         isUnique (IL.ForeignDecl f _ _ _) = isRenamed (unqualify f)
> cleanDebug False m = m

> dataTypes :: TCEnv -> [(Cam.Name,[Cam.Name])]
> dataTypes tcEnv = [dataType tc cs | DataType tc _ cs <- allEntities tcEnv]
>   where dataType tc cs = (con tc,map (con . qualifyLike tc) cs)

> writeCode :: Maybe FilePath -> FilePath -> Either CFile [CFile] -> IO ()
> writeCode tfn sfn (Left cfile) = writeCCode ofn cfile
>   where ofn = fromMaybe (rootname sfn ++ cExt) tfn
> writeCode tfn sfn (Right cfiles) = zipWithM_ (writeCCode . mkFn) [1..] cfiles
>   where prefix = fromMaybe (rootname sfn) tfn
>         mkFn i = prefix ++ show i ++ cExt

> writeGoalCode :: Maybe FilePath -> CFile -> IO ()
> writeGoalCode tfn = writeCCode ofn
>   where ofn = fromMaybe (internalError "No filename for startup code") tfn

> writeCCode :: FilePath -> CFile -> IO ()
> writeCCode fn = writeFile fn . showLn . CPretty.ppCFile
>   where showLn = fullRender LeftMode undefined undefined cat "\n"
>         cat (Chr c) = showChar c
>         cat (Str cs) = showString cs
>         cat (PStr cs) = showString cs

> cExt :: String
> cExt = ".c"

\end{verbatim}
The \texttt{doDump} function writes the selected information to the
standard output.
\begin{verbatim}

> doDump :: Options -> (Dump,Doc) -> IO ()
> doDump opts (d,x) =
>   when (d `elem` dump opts)
>        (print (text hd $$ text (replicate (length hd) '=') $$ x))
>   where hd = dumpHeader d

> dumpHeader :: Dump -> String
> dumpHeader DumpRenamed = "Module after renaming"
> dumpHeader DumpTypes = "Types"
> dumpHeader DumpDesugared = "Source code after desugaring"
> dumpHeader DumpUnlabeled = "Source code after removing field labels"
> dumpHeader DumpNewtype = "Source code after removing newtypes"
> dumpHeader DumpUnlazy = "Source code after lifting lazy patterns"
> dumpHeader DumpFlatCase = "Source code after case flattening"
> dumpHeader DumpSimplified = "Source code after simplification"
> dumpHeader DumpPBU = "Source code with pattern binding updates"
> dumpHeader DumpDict = "Source code with dictionaries"
> dumpHeader DumpSpecialize = "Source code after specialization"
> dumpHeader DumpLifted = "Source code after lifting"
> dumpHeader DumpIL = "Intermediate code"
> dumpHeader DumpTransformed = "Transformed code" 
> dumpHeader DumpNormalized = "Intermediate code after normalization"
> dumpHeader DumpCam = "Abstract machine code"

\end{verbatim}
The function \texttt{ppTypes} is used for pretty-printing the types
from the type environment.
\begin{verbatim}

> ppTypes :: TCEnv -> [(Ident,ValueInfo)] -> Doc
> ppTypes tcEnv = vcat . map ppInfo
>   where ppInfo (c,DataConstructor _ _ _ ty) =
>           ppType c ty <+> text "-- data constructor"
>         ppInfo (c,NewtypeConstructor _ _ ty) =
>           ppType c ty <+> text "-- newtype constructor"
>         ppInfo (x,Value _ _ ty) = ppType x ty
>         ppType f ty = ppIdent f <+> text "::" <+> ppTypeScheme tcEnv ty

\end{verbatim}
