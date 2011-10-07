% -*- LaTeX -*-
% $Id: Options.lhs 3055 2011-10-07 15:44:49Z wlux $
%
% Copyright (c) 2001-2011, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Options.lhs}
\section{Compiler options}
\begin{verbatim}

> module Options where
> import GetOpt

\end{verbatim}
A record of type \texttt{Options} is used to gather the settings of
all compiler options.
\begin{verbatim}

> data Options =
>   Options {
>     importPath :: [FilePath],         -- directories for searching imports
>     output :: Maybe FilePath,         -- name of output file
>     goal :: Maybe (Maybe String),     -- goal to be evaluated
>     typeIt :: Maybe String,           -- goal to be typed
>     noInterface :: Bool,              -- do not create an interface file
>     splitCode :: Bool,                -- split object code
>     debug :: Bool,                    -- add debugging transformation
>     trusted :: Bool,                  -- trusted module for debugging
>     caseMode :: CaseMode,             -- case mode
>     warn :: [Warn],                   -- warnings
>     dump :: [Dump]                    -- dumps
>   }
>   deriving Show

> defaultOptions =
>   Options{
>     importPath = [],
>     output = Nothing,
>     goal = Nothing,
>     typeIt = Nothing,
>     noInterface = False,
>     splitCode = False,
>     debug = False,
>     trusted = False,
>     caseMode = FreeMode,
>     warn = [],
>     dump = []
>   }

> data CaseMode =
>   FreeMode | HaskellMode | PrologMode | GoedelMode
>   deriving (Eq,Show)

> data Warn =
>     WarnUnusedData                    -- warnings for unused data constructors
>   | WarnUnusedDecl                    -- warnings for unused declarations
>   | WarnUnusedVar                     -- warnings for all unused variables
>   | WarnShadow                        -- warnings for shadowing definitions
>   | WarnOverlap                       -- warnings for overlapping patterns
>   deriving (Eq,Bounded,Enum,Show)

> minUnused, maxUnused :: Warn
> minUnused = WarnUnusedData
> maxUnused = WarnUnusedVar

> data Dump =
>     DumpRenamed                       -- dump source after renaming
>   | DumpTypes                         -- dump types after typechecking
>   | DumpDesugared                     -- dump source after desugaring
>   | DumpUnlabeled                     -- dump source after removing labels
>   | DumpNewtype                       -- dump source after removing newtypes
>   | DumpUnlazy                        -- dump source after lifting lazy patt.
>   | DumpFlatCase                      -- dump source after case flattening
>   | DumpSimplified                    -- dump source after simplification
>   | DumpPBU                           -- dump source with pattern updates
>   | DumpDict                          -- dump source with dictionaries
>   | DumpSpecialize                    -- dump source after specialization
>   | DumpLifted                        -- dump source after lambda-lifting
>   | DumpIL                            -- dump IL code after translation
>   | DumpTransformed                   -- dump transformed code
>   | DumpNormalized                    -- dump IL code after normalization
>   | DumpCam                           -- dump abstract machine code
>   deriving (Eq,Bounded,Enum,Show)

\end{verbatim}
The \texttt{Option} type maps every command line switch on a data
constructor. This is needed in order to use the \texttt{GetOpt}
library.
\begin{verbatim}

> data Option =
>     Help
>   | ImportPath FilePath | Output FilePath
>   | Eval (Maybe String) | Type String
>   | SplitCode | NoInterface | Debug | Trusted
>   | CaseMode CaseMode | Warn [Warn] | Dump [Dump]
>   deriving (Eq,Show)

\end{verbatim}
The global variable \texttt{options} defines all options which are
recognized by the compiler.
\begin{verbatim}

> options = [
>     Option "i" ["import-dir"] (ReqArg ImportPath "DIR")
>            "search for imports in DIR",
>     Option "e" ["eval"] (OptArg Eval "GOAL")
>            "generate code to evaluate GOAL",
>     Option "t" ["type"] (ReqArg Type "GOAL")
>            "compute type of GOAL",
>     Option "o" ["output"] (ReqArg Output "FILE")
>            "write code or type to FILE",
>     Option "" ["no-icurry"] (NoArg NoInterface)
>            "do not create an interface file",
>     Option "" ["split-code"] (NoArg SplitCode)
>            "emit one C file for each function",
>     Option "g" ["debug"] (NoArg Debug)
>            "transform code for debugging",
>     Option "" ["trusted"] (NoArg Trusted)
>            "trust this module (if compiled with -g/--debug)",
>     Option "" ["haskell-mode"] (NoArg (CaseMode HaskellMode))
>            "use Haskell naming conventions",
>     Option "" ["prolog-mode"] (NoArg (CaseMode PrologMode))
>            "use Prolog naming conventions",
>     Option "" ["goedel-mode"] (NoArg (CaseMode GoedelMode))
>            "use Goedel naming conventions",
>     Option "" ["warn-all"] (NoArg (Warn [minBound..maxBound]))
>            "enable all warnings",
>     Option "" ["warn-unused"] (NoArg (Warn [minUnused..maxUnused]))
>            "enable all unused warnings",
>     Option "" ["warn-unused-data"] (NoArg (Warn [WarnUnusedData]))
>            "enable unused data constructor warnings",
>     Option "" ["warn-unused-decls"] (NoArg (Warn [WarnUnusedDecl]))
>            "enable unused declaration warnings",
>     Option "" ["warn-unused-vars"] (NoArg (Warn [WarnUnusedVar]))
>            "enable unused variable warnings",
>     Option "" ["warn-shadow"] (NoArg (Warn [WarnShadow]))
>            "enable shadowing definitions warnings",
>     Option "" ["warn-overlap"] (NoArg (Warn [WarnOverlap]))
>            "enable overlapping patterns warnings",
>     Option "" ["dump-all"] (NoArg (Dump [minBound..maxBound]))
>            "dump everything",
>     Option "" ["dump-renamed"] (NoArg (Dump [DumpRenamed]))
>            "dump source code after renaming",
>     Option "" ["dump-types"] (NoArg (Dump [DumpTypes]))
>            "dump types after type-checking",
>     Option "" ["dump-desugared"] (NoArg (Dump [DumpDesugared]))
>            "dump source code after desugaring",
>     Option "" ["dump-unlabeled"] (NoArg (Dump [DumpUnlabeled]))
>            "dump source code after removing field labels",
>     Option "" ["dump-newremoved"] (NoArg (Dump [DumpNewtype]))
>            "dump source code after removing newtypes",
>     Option "" ["dump-unlazy"] (NoArg (Dump [DumpUnlazy]))
>            "dump source code after lifting lazy patterns",
>     Option "" ["dump-flattened"] (NoArg (Dump [DumpFlatCase]))
>            "dump source code after case flattening",
>     Option "" ["dump-simplified"] (NoArg (Dump [DumpSimplified]))
>            "dump source code after simplification",
>     Option "" ["dump-pbu"] (NoArg (Dump [DumpPBU]))
>            "dump source code with pattern binding updates",
>     Option "" ["dump-dict"] (NoArg (Dump [DumpDict]))
>            "dump source code with dictionaries",
>     Option "" ["dump-specialize"] (NoArg (Dump [DumpSpecialize]))
>            "dump source code after specialization",
>     Option "" ["dump-lifted"] (NoArg (Dump [DumpLifted]))
>            "dump source code after lambda-lifting",
>     Option "" ["dump-il"] (NoArg (Dump [DumpIL]))
>            "dump intermediate language before lifting",
>     Option "" ["dump-transformed"] (NoArg (Dump [DumpTransformed]))
>            "dump IL code after debugging transformation",
>     Option "" ["dump-normalized"] (NoArg (Dump [DumpNormalized]))
>            "dump IL code after normalization",
>     Option "" ["dump-cam"] (NoArg (Dump [DumpCam]))
>            "dump abstract machine code",
>     Option "?h" ["help"] (NoArg Help)
>            "display this help and exit"
>   ]

\end{verbatim}
The function \texttt{selectOption} applies an \texttt{Option} to an
\texttt{Options} record. Note that there is no case for
\texttt{Help}. If the user asks for help, the compiler will simply
print its usage message and terminate.
\begin{verbatim}

> selectOption :: Option -> Options -> Options
> selectOption (ImportPath dir) opts =
>   opts{ importPath = dir : importPath opts }
> selectOption (Output file) opts = opts{ output = Just file }
> selectOption (Eval goal) opts = opts{ goal = Just goal }
> selectOption (Type goal) opts = opts{ typeIt = Just goal }
> selectOption NoInterface opts = opts{ noInterface = True }
> selectOption SplitCode opts = opts{ splitCode = True }
> selectOption Debug opts = opts{ debug = True }
> selectOption Trusted opts = opts{ trusted = True }
> selectOption (CaseMode cm) opts = opts{ caseMode = cm }
> selectOption (Warn ws) opts = opts{ warn = ws ++ warn opts }
> selectOption (Dump ds) opts = opts{ dump = ds ++ dump opts }

\end{verbatim}
