% -*- LaTeX -*-
% $Id: cam2c.lhs 3220 2016-06-15 22:32:30Z wlux $
%
% Copyright (c) 2005-2015, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{cam2c.lhs}
\section{Compiling Abstract Machine Code}
This file defines the main module of an abstract machine code into C
compiler.
\begin{verbatim}

> import Cam
> import CamParser
> import CGen
> import CCode
> import CPretty
> import Files
> import Error
> import GetOpt
> import IO
> import List
> import Maybe
> import Monad
> import Pretty                -- required to import Show Doc instance with hbc
> import System
> import Utils

> main :: IO ()
> main =
>   do
>     prog <- getProgName
>     args <- getArgs
>     importPath <- getCurryImportPath
>     cam2c prog args importPath

\end{verbatim}
The main program acts as a traditional Unix filter program, i.e., it
reads abstract machine code from the standard input and writes the
compiled C code to the standard output by default. It is possible to
specify one or more abstract machine code files on the command line,
which are read instead of standard input, and to specify an output
file with the \texttt{-o} switch. If \texttt{-o} occurs more than once
on the command line, we use the last occurrence.
\begin{verbatim}

> cam2c :: String -> [String] -> [ImportPath] -> IO ()
> cam2c prog args curryImportPath
>   | Help `elem` opts = printUsage prog
>   | null errs =
>       case goals opts of
>         [] -> compileFiles importPath (outputFile opts) files Nothing
>         [g] -> compileFiles importPath (outputFile opts) files (Just g)
>         _ -> badUsage prog ["Multiple goal options not allowed"]
>   | otherwise = badUsage prog errs
>   where (opts,files,errs) = getOpt Permute options args
>         importPath = importPaths opts ++ curryImportPath

> printUsage :: String -> IO ()
> printUsage prog =
>   do
>     putStrLn (usageInfo (unlines header) options)
>     exitWith ExitSuccess
>   where header = ["usage: " ++ prog ++ " [OPTION]... SCRIPT..."]

> badUsage :: String -> [String] -> IO ()
> badUsage prog errs =
>   do
>     mapM_ (putErr . mkErrorLine) errs
>     putErrLn ("Try `" ++ prog ++ " --help' for more information")
>     exitWith (ExitFailure 1)
>   where mkErrorLine err = prog ++ ": " ++ err

> importPaths :: [Option] -> [ImportPath]
> importPaths opts = [ImpDir d | ImportPath d <- opts]

> outputFile :: [Option] -> Maybe FilePath
> outputFile opts
>   | null fns = Nothing
>   | otherwise = Just (last fns)
>   where fns = [fn | Output fn <- opts]

> goals :: [Option] -> [(String,Maybe [String])]
> goals = foldr goal []
>   where goal (Goal g) gs = (f,Just vs) : gs where (f:vs) = words g
>         goal (IO f) gs = (f,Nothing) : gs
>         goal _ gs = gs

\end{verbatim}
Besides the \texttt{-o} switch, the compiler understands a few more
options. In particular, it is possible to generate entry code for a
goal with the \texttt{-e} switch. By default, the goal is evaluated in
global search mode. In order to force execution as a monadic program,
the \texttt{-m} switch must be used in conjunction with \texttt{-e}.
\begin{verbatim}

> data Option =
>     ImportPath FilePath
>   | Output FilePath
>   | Goal String
>   | IO String
>   | Help
>   deriving (Eq,Show)

> options :: [OptDescr Option]
> options = [
>     Option "e"  ["eval"] (ReqArg Goal "GOAL")
>            "evaluate GOAL (syntax: FN VAR...)",
>     Option "i"  ["import-dir"] (ReqArg ImportPath "DIR")
>            "search imported modules in DIR",
>     Option "m"  ["io"] (ReqArg IO "GOAL")
>            "execute monadic GOAL (syntax: FN)",
>     Option "o"  ["output"] (ReqArg Output "FILE")
>            "write C code to FILE",
>     Option "?h" ["help"] (NoArg Help)
>            "display this help and exit"
>   ]

\end{verbatim}
If no input file was specified on the command line, the compiler reads
an abstract machine code module from the standard input. Otherwise,
the contents of all files specified on the command line is merged into
a single abstract machine code module. For each file, the compiler
recursively loads the imported modules in order to resolve data
constructor tags in the code.
\begin{verbatim}

> compileFiles :: [ImportPath] -> Maybe FilePath -> [FilePath]
>              -> Maybe (String, Maybe [String]) -> IO ()
> compileFiles importPath ofn fns g =
>   do
>     cam <- if null fns then parseInput else parseFiles fns
>     let (ms,_,_) = splitCam cam
>     cam' <- mapM (lookupModule importPath) ms >>= parseFiles
>     let ts = [(tc,map constr cs) | DataDecl tc _ cs <- cam ++ cam']
>     let ccode =
>           maybe id (flip mergeCFile . uncurry genGoal) g (genModule ts cam)
>     maybe putStr writeFile ofn $ showLn $ ppCFile ccode
>   where constr (ConstrDecl _ c _) = c

> genGoal :: String -> Maybe [String] -> CFile
> genGoal f (Just vs) =
>   genModule [] [FunctionDecl Exported f' vs' st] ++ genMain f' (Just vs)
>   where f' = Name "curry_eval"
>         vs' = Name "_1" : map Name vs
>         st =
>           Seq (Name "_2" :<- Return (Closure (Name f) (map Name vs)))
>               (Exec (mangle "=:=") [Name "_1",Name "_2"])
> genGoal f Nothing = genMain (Name f) Nothing

> parseInput :: IO Module
> parseInput = liftM (ok . parseModule "") getContents

> parseFiles :: [FilePath] -> IO Module
> parseFiles fns = liftM concat (mapM parseFile fns)

> parseFile :: FilePath -> IO Module
> parseFile fn = liftM (ok . parseModule fn) (readFile fn)

> lookupModule :: [ImportPath] -> Name -> IO FilePath
> lookupModule importPath m =
>   lookupFile (filesInPath (ImpDir "" : importPath) fn) >>=
>   maybe (ioError (userError (fileNotFound fn))) return
>   where fn = demangle m ++ ".cam"

> fileNotFound :: FilePath -> String
> fileNotFound fn = "File " ++ show fn ++ " not found in import path"

\end{verbatim}
