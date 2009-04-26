% -*- LaTeX -*-
% $Id: Common.lhs 2803 2009-04-26 17:14:20Z wlux $
%
% Copyright (c) 1999-2009, Wolfgang Lux
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
> import Unlambda
> import Utils
> import ValueInfo

\end{verbatim}
The first transformation phase prepares the code for being translated
into the intermediate language. The transformation stops after
simplifying the code and naming lambda abstractions in order to
eventually update the module's interface.
\begin{verbatim}

> transModule :: Bool -> Trust -> TCEnv -> ValueEnv -> Module Type
>             -> (TCEnv,ValueEnv,TrustEnv,Module Type,[(Dump,Doc)])
> transModule debug tr tcEnv tyEnv m =
>   (tcEnv',tyEnv'''''''',trEnv,nolambda,dumps)
>   where trEnv = if debug then trustEnv tr m else emptyEnv
>         (desugared,tyEnv') = desugar tyEnv m
>         (unlabeled,tyEnv'') = unlabel tcEnv tyEnv' desugared
>         (nonewtype,tcEnv',tyEnv''') = transNewtype tcEnv tyEnv'' unlabeled
>         (nolazy,tyEnv'''') = unlazy tyEnv''' nonewtype
>         (flatCase,tyEnv''''') = caseMatch tcEnv' tyEnv'''' nolazy
>         (simplified,tyEnv'''''') = simplify tcEnv' tyEnv''''' trEnv flatCase
>         (pbu,tyEnv''''''') = pbTrans tyEnv'''''' simplified
>         (nolambda,tyEnv'''''''') = unlambda tyEnv''''''' pbu
>         dumps =
>           [(DumpRenamed,ppModule m),
>            (DumpTypes,ppTypes tcEnv (localBindings tyEnv)),
>            (DumpDesugared,ppModule desugared),
>            (DumpUnlabeled,ppModule unlabeled),
>            (DumpNewtype,ppModule nonewtype),
>            (DumpUnlazy,ppModule nolazy),
>            (DumpFlatCase,ppModule flatCase),
>            (DumpSimplified,ppModule simplified),
>            (DumpPBU,ppModule pbu),
>            (DumpUnlambda,ppModule nolambda)]

\end{verbatim}
After creating the module's interface, the compiler introduces
explicit dictionary arguments for overloaded functions and methods.
\begin{verbatim}

> dictTrans :: TCEnv -> InstEnv -> ValueEnv -> Module Type
>           -> (TCEnv,ValueEnv,Module Type,[(Dump,Doc)])
> dictTrans tcEnv iEnv tyEnv m = (tcEnv',tyEnv',spec,dumps)
>   where (tcEnv',tyEnv',dict) = dictTransModule tcEnv iEnv tyEnv m
>         spec = dictSpecializeModule tcEnv' dict
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
>   where (lifted,tyEnv',trEnv') = lift tyEnv trEnv m
>         il = ilTrans tcEnv tyEnv' lifted
>         ilDbg
>           | debug = debugAddMain (dTransform (trustedFun trEnv') il)
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
\begin{verbatim}

> genCodeModule :: Bool -> TCEnv -> IL.Module
>               -> (Either CFile [CFile],[(Dump,Doc)])
> genCodeModule False tcEnv il = (Left ccode,dumps)
>   where (ccode,dumps) = genCode (dataTypes tcEnv) il
> genCodeModule True tcEnv il = (Right ccode,concat (transpose dumps))
>   where (ccode,dumps) =
>           unzip $ map (genCode (dataTypes tcEnv)) (splitModule il)

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

> trustedFun :: TrustEnv -> QualIdent -> Bool
> trustedFun trEnv f = maybe True (Trust ==) (lookupEnv (unqualify f) trEnv)

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
> dumpHeader DumpUnlambda = "Source code after naming lambdas"
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
