-- $Id: cymk.hs 3220 2016-06-15 22:32:30Z wlux $
--
-- Copyright (c) 2002-2015, Wolfgang Lux
-- See LICENSE for the full license.

import CurryDeps
import Files
import GetOpt
import IO
import Maybe
import Monad
import System
import Utils

data Options =
  Options{
    importPaths :: [ImportPath],
    output :: Maybe FilePath,
    goal :: Maybe String,
    debug :: Bool,
    mkDepend :: Bool,
    mkClean :: Bool,
    find :: Bool
  }

defaultOptions =
  Options{
    importPaths = [],
    output = Nothing,
    goal = Nothing,
    debug = False,
    mkDepend = False,
    mkClean = False,
    find = False
  }

data Option =
    Help | ImportPath FilePath | LibPath FilePath | Output FilePath
  | Goal String | Debug | Clean | Depend | Find
  deriving Eq

options = [
    Option "g" ["debug"] (NoArg Debug)
           "compile with debugging information",
    Option "i" ["import-dir"] (ReqArg ImportPath "DIR")
           "search for imported modules in DIR",
    Option "M" ["depend"] (NoArg Depend)
           "create Makefile dependencies for all targets",
    Option "o" ["output"] (ReqArg Output "FILE")
           "output goes to FILE",
    Option "e" ["goal"] (ReqArg Goal "GOAL")
           "executable evaluates GOAL",
    Option "P" ["lib-dir"] (ReqArg LibPath "DIR")
           "search for library interfaces in DIR",
    Option ""  ["clean"] (NoArg Clean)
           "remove compiled file for all targets",
    Option ""  ["find"] (NoArg Find)
           "find source/interface for all targets",
    Option "?h" ["help"] (NoArg Help)
           "display this help and exit"
  ]

selectOption (ImportPath dir) opts =
  opts{ importPaths = ImpDir dir : importPaths opts }
selectOption (LibPath dir) opts =
  opts{ importPaths = LibDir dir : importPaths opts }
selectOption (Output file) opts = opts{ output = Just file }
selectOption (Goal g) opts = opts{ goal = Just g }
selectOption Debug opts = opts{ debug = True }
selectOption Depend opts = opts{ mkDepend = True }
selectOption Clean opts = opts{ mkClean = True }
selectOption Find opts = opts{ find = True }

main :: IO ()
main =
  do
    prog <- getProgName
    args <- getArgs
    importPath <- getCurryImportPath
    cymk prog args importPath

cymk :: String -> [String] -> [ImportPath] -> IO ()
cymk prog args curryImportPath
  | Help `elem` opts = printUsage prog
  | null errs = processFiles cymkOpts prog files
  | otherwise = badUsage prog errs
  where (opts,files,errs) = getOpt Permute options args
        cymkOpts =
	  foldr selectOption
                defaultOptions{ importPaths = curryImportPath }
                opts

printUsage :: String -> IO ()
printUsage prog =
  do
    putStrLn (usageInfo (unlines header) options)
    exitWith ExitSuccess
  where header = ["usage: " ++ prog ++ " [OPTION]... MODULE ..."]

badUsage :: String -> [String] -> IO ()
badUsage prog errs =
  do
    mapM_ (putErr . mkErrorLine) errs
    putErrLn ("Try `" ++ prog ++ " --help' for more information")
    exitWith (ExitFailure 1)
  where mkErrorLine err = prog ++ ": " ++ err

processFiles :: Options -> String -> [String] -> IO ()
processFiles opts prog files
  | null files = badUsage prog ["no modules\n"]
  | length (filter id [mkDepend opts,mkClean opts,find opts]) > 1 =
      badUsage prog ["cannot mix --clean, --depend, and --find\n"]
  | mkDepend opts = makeDepend (importPaths opts) (output opts) files
  | find opts = findModules (importPaths opts) (output opts) files
  | isJust (output opts) && length files > 1 =
      badUsage prog ["cannot specify -o with multiple targets\n"]
  | otherwise =
      do
        es <- fmap concat (mapM script files)
	unless (null es) (mapM putErrLn es >> exitWith (ExitFailure 2))
  where script = buildScript (mkClean opts) (debug opts) (importPaths opts)
			     (goal opts) (output opts)
