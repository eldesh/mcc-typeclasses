% -*- LaTeX -*-
% $Id: mach.lhs 1912 2006-05-03 14:53:33Z wlux $
%
% Copyright (c) 1998-2006, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{mach.lhs}
\section{A little front-end for the abstract machine}
This section contains a little front-end, that can be used to execute
abstract machine programs. Its main function will accept a list of
filenames as arguments. These files are loaded, the goal will then be
reduced to normal form and finally the result is printed. Several
options allow to specify the trace function to be used and to select
the name of the goal to be reduced. The options {\tt -i} offers the
possibility to enter a little interactive top-level.
\begin{verbatim}

> import CamParser
> import MachInterp
> import MachLoader
> import Char
> import GetOpt
> import Monad
> import Error
> import Combined
> import IO
> import System

> data Option =
>     Help
>   | Goal String               -- goal to be evaluated
>   | Monadic                   -- evalute monadic goal (IO)
>   | TraceKind TraceKind       -- select tracing level
>   | Quiet                     -- no output during loading
>   | Verbose                   -- verbose output during loading
>   | Interactive               -- run interactive top-level
>   deriving Eq

> data TraceKind = NoTrace | InstrTrace | AbbrevStackTrace | FullStackTrace
>                  deriving (Eq,Read,Show)

> data MachOpts = MachOpts {
>     goal        :: String,
>     args        :: [String],
>     monadic     :: Bool,
>     traceKind   :: TraceKind,
>     verbose     :: Bool,
>     mainFunc    :: MachOpts -> (ConstrEnv,FunEnv) -> [String] -> IO ()
>   }

> defaultGoal :: String
> defaultGoal = "main.main"

> defaultOpts = MachOpts defaultGoal [] False NoTrace True execProg

> options :: [OptDescr Option]
> options = [
>     Option "g" ["goal"] (ReqArg Goal "GOAL")
>            ("evaluate GOAL (default: " ++ defaultGoal ++ ")"),
>     Option "i" ["interactive"] (NoArg Interactive)
>            "enter interactive top-level",
>     Option "m" ["io"] (NoArg Monadic)
>            "the goal is of type IO ()",
>     Option "q" ["quiet"] (NoArg Quiet)
>            "do not show script names during loading",
>     Option "s" ["stack","abbrev-stack"] (NoArg (TraceKind AbbrevStackTrace))
>            "like -t but dump stack contents",
>     Option "S" ["full-stack"] (NoArg (TraceKind FullStackTrace))
>            "like -s but more verbose",
>     Option "t" ["trace"] (NoArg (TraceKind InstrTrace))
>            "trace instructions during execution",
>     Option "v" ["verbose"] (NoArg Verbose)
>            "show script names during loading",
>     Option "?h" ["help"] (NoArg Help)
>            "display this help and exit"
>  ]

> main :: IO ()
> main =
>   do
>     prog <- getProgName
>     args <- getArgs
>     mach prog args

> mach :: String -> [String] -> IO ()
> mach prog args
>   | Help `elem` opts = printUsage prog
>   | not (null errs) = badUsage prog errs
>   | not (null errs') = badUsage prog errs
>   | otherwise = mainFunc opts' opts' (initConstrEnv,initFunEnv) scripts
>   where (opts,scripts,errs) = getOpt RequireOrder options args
>         (opts',errs') = selectOptions opts defaultOpts

> printUsage :: String -> IO ()
> printUsage prog =
>   do
>     putStrLn (usageInfo (unlines header) options)
>     exitWith (ExitSuccess)
>   where header = ["usage: " ++ prog ++ " [OPTION]... SCRIPT..."]

> badUsage :: String -> [String] -> IO ()
> badUsage prog errs =
>   do
>     mapM_ (putStr . mkErrorLine) errs
>     putErrLn ("Try `" ++ prog ++ " --help' for more information")
>     exitWith (ExitFailure 1)
>   where mkErrorLine err = prog ++ ": " ++ err

> selectOptions :: [Option] -> MachOpts -> (MachOpts,[String])
> selectOptions [] opts = (opts,[])
> selectOptions (o:os) opt = procNextOpt o opt'
>   where procNextOpt (Goal g) opts =
>           case words g of
>             []     -> (opts,emptyGoalErr:errs)
>             (g:vs) -> (opts{ goal=g, args=vs },errs)
>         procNextOpt Monadic opts = (opts{ monadic = True },errs)
>         procNextOpt (TraceKind k) opts = (opts{ traceKind = k },errs)
>         procNextOpt Quiet opts = (opts{ verbose = False },errs)
>         procNextOpt Verbose opts = (opts {verbose = True },errs)
>         procNextOpt Interactive opts = (opts { mainFunc = toplevel },errs)
>
>         (opt',errs) = selectOptions os opt

> emptyGoalErr :: String
> emptyGoalErr = "null goal specified\n"

> execProg :: MachOpts -> (ConstrEnv,FunEnv) -> [String] -> IO ()
> execProg opts inienv scripts =
>   do
>     env <- readScripts (verbose opts) (tracer opts) inienv scripts
>     evaluateGoal (monadic opts) (goal opts) (args opts) env

> toplevel :: MachOpts -> (ConstrEnv,FunEnv) -> [String] -> IO ()
> toplevel opts inienv scripts =
>   do
>     env <- readScripts (verbose opts) (tracer opts) inienv scripts
>     toploop opts env env
>   where toploop opts inienv curenv =
>           do
>             putStr "? "
>             hFlush stdout
>             command <- getLine
>             interpretCommand opts inienv curenv (lex command)
>         interpretCommand opts inienv curenv [(cmd,args)] =
>           maybe noCommand id (lookup cmd commandTable)
>                 opts inienv curenv (dropWhile isSpace args)
>         interpretCommand opts inienv curenv _ =
>           showQuickHelp opts inienv curenv
>         noCommand opts inienv curenv _ = showQuickHelp opts inienv curenv
>         emptyCommand opts inienv curenv _ = toploop opts inienv curenv
>         helpCommand opts inienv curenv _ = showHelp opts inienv curenv
>         loadCommand opts inienv curenv "" = showQuickHelp opts inienv curenv
>         loadCommand opts inienv curenv s@('\"':_) =
>           case (reads s :: [(String, String)]) of
>             [(script, _)] -> alsoCommand1 opts inienv inienv script
>             _ -> do putStrLn "parse error"; toploop opts inienv curenv
>         loadCommand opts inienv _ s = alsoCommand1 opts inienv inienv script
>           where (script,_) = break isSpace s
>         alsoCommand opts inienv curenv "" = showQuickHelp opts inienv curenv
>         alsoCommand opts inienv curenv s@('\"':_) =
>           case (reads s :: [(String, String)]) of
>             [(script, _)] -> alsoCommand1 opts inienv curenv script
>             _ -> do putStrLn "parse error"; toploop opts inienv curenv
>         alsoCommand opts inienv curenv s =
>           alsoCommand1 opts inienv curenv script
>           where (script,_) = break isSpace s
>         alsoCommand1 opts inienv curenv script =
>           catch (readScript (verbose opts) (tracer opts) curenv script)
>                 (\e -> do putStrLn (show e); return curenv) >>=
>           toploop opts inienv
>         evalCommand opts inienv curenv s =
>           do
>             case words s of
>               [] -> evaluateGoal False (goal opts) (args opts) curenv
>               (goal:args) -> evaluateGoal False goal args curenv
>             toploop opts inienv curenv
>         ioCommand opts inienv curenv s =
>           do
>             case words s of
>               [] -> evaluateGoal True (goal opts) [] curenv
>               (goal:_) -> evaluateGoal True goal [] curenv
>             toploop opts inienv curenv
>         traceCommand opts inienv curenv args =
>           case lex args of
>             [(arg, _)] -> traceCommand1 opts inienv curenv arg
>             _ -> do putStrLn "parse error"; toploop opts inienv curenv
>         traceCommand1 opts inienv curenv arg
>           | arg == "" =
>               do
>                 putStrLn ("current tracer is: " ++ show (traceKind opts))
>                 toploop opts inienv curenv
>           | arg == "on" =
>               toploop opts{ traceKind = InstrTrace } inienv curenv
>           | arg == "stack" =
>               toploop opts { traceKind = AbbrevStackTrace } inienv curenv
>           | arg == "full" =
>               toploop opts { traceKind = FullStackTrace } inienv curenv
>           | arg == "off" = toploop opts{ traceKind = NoTrace } inienv curenv
>           | otherwise =
>               case reads arg of
>                 [(kind, _)] -> toploop opts{ traceKind = kind } inienv curenv
>                 _ -> do putStrLn "invalid trace kind"
>                         toploop opts inienv curenv
>         quitCommand _ _ _ _ = return ()
>         showQuickHelp opts inienv curenv =
>           do
>             putStrLn "Enter `help' for help"
>             toploop opts inienv curenv
>         showHelp opts inienv curenv =
>           do
>             mapM_ putStrLn [
>                 "Valid commands:",
>                 " help                      show this help text",
>                 " load <script>             load script into initial environment",
>                 " also <script>             load script into current environment",
>                 " eval <goal> <var>...      evaluate goal",
>                 " io <goal>                 evaluate monadic goal (IO ())",
>                 " trace [on|stack|full|off] enable/disable tracing"
>               ]
>             toploop opts inienv curenv
>         commandTable = [("", emptyCommand), ("help", helpCommand),
>                         ("load", loadCommand), ("also", alsoCommand),
>                         ("eval", evalCommand), ("io", ioCommand),
>                         ("trace", traceCommand), ("quit", quitCommand)]

> readScripts :: Bool -> Maybe Instrument -> (ConstrEnv,FunEnv) -> [String]
>             -> IO (ConstrEnv,FunEnv)
> readScripts verbose tracer = foldM (readScript verbose tracer)

> readScript :: Bool -> Maybe Instrument -> (ConstrEnv,FunEnv) -> String
>             -> IO (ConstrEnv,FunEnv)
> readScript True tracer (cEnv,fEnv) script =
>   do
>     putErr ("Loading " ++ script ++ " ...")
>     (cEnv',fEnv') <- readScript False tracer (cEnv,fEnv) script
>     putErrLn " done"
>     return (cEnv',fEnv')
> readScript False tracer (cEnv,fEnv) script =
>   do
>     s <- readFile script
>     case parseModule script s of
>       Ok p -> return (loadModule tracer cEnv fEnv p)
>       Errors msgs -> do mapM_ putErrLn msgs; return (cEnv,fEnv)

> evaluateGoal :: Bool -> String -> [String] -> (ConstrEnv,FunEnv) -> IO ()
> evaluateGoal monadic goal vars (cEnv,fEnv) =
>   callErr (evaluate (function goal fEnv)) >>= showResult
>   where evaluate (Just goal)
>           | monadic = startIO goal
>           | otherwise = start goal vars
>         evaluate Nothing = fail ("undefined goal: " ++ show goal)
>         showResult (Ok result) = putStr (result "")
>         showResult (Errors msgs) =
>           do
>             putErrLn ""
>             mapM_ (putErrLn . ("ERROR: " ++)) msgs
>             putErrLn ""

> tracer :: MachOpts -> Maybe Instrument
> tracer opts = tracer' (traceKind opts)
>   where tracer' NoTrace = Nothing
>         tracer' InstrTrace = Just traceInstr
>         tracer' AbbrevStackTrace = Just (traceStack (dumpPtr 1))
>         tracer' FullStackTrace = Just (traceStack (dumpPtr 25))

> putErr, putErrLn :: String -> IO ()
> putErr = hPutStr stderr
> putErrLn = hPutStr stderr . (++ "\n")

\end{verbatim}
