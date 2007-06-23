-- $Id: cymk.hs 2364 2007-06-23 13:42:09Z wlux $
--
-- Copyright (c) 2002-2007, Wolfgang Lux
-- See LICENSE for the full license.

import CurryDeps
import GetOpt
import Maybe
import Monad
import IO
import PathUtils
import System

data Options =
  Options{
    importPaths :: [(Bool,FilePath)],
    output :: Maybe FilePath,
    debug :: Bool,
    linkAlways :: Bool,
    mkDepend :: Bool,
    mkClean :: Bool,
    find :: Bool
  }

defaultOptions =
  Options{
    importPaths = [],
    output = Nothing,
    debug = False,
    linkAlways = False,
    mkDepend = False,
    mkClean = False,
    find = False
  }

data Option =
    Help | ImportPath FilePath | LibPath FilePath | Output FilePath
  | Debug | LinkAlways | Clean | Depend | Find
  deriving Eq

options = [
    Option "a" ["link-always"] (NoArg LinkAlways)
           "always relink the target file",
    Option "g" ["debug"] (NoArg Debug)
           "compile with debugging information",
    Option "i" ["import-dir"] (ReqArg ImportPath "DIR")
           "search for imported modules in DIR",
    Option "M" ["depend"] (NoArg Depend)
           "create Makefile dependencies for all targets",
    Option "o" ["output"] (ReqArg Output "FILE")
           "output goes to FILE",
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
  opts{ importPaths = (True,dir) : importPaths opts }
selectOption (LibPath dir) opts =
  opts{ importPaths = (False,dir) : importPaths opts }
selectOption (Output file) opts = opts{ output = Just file }
selectOption Debug opts = opts{ debug = True }
selectOption LinkAlways opts = opts{ linkAlways = True }
selectOption Depend opts = opts{ mkDepend = True }
selectOption Clean opts = opts{ mkClean = True }
selectOption Find opts = opts{ find = True }

main :: IO ()
main =
  do
    prog <- getProgName
    args <- getArgs
    importPath <- catch (getEnv "CURRY_IMPORT_PATH" >>= return . pathList)
                        (const (return []))
    cymk prog args importPath

cymk :: String -> [String] -> [FilePath] -> IO ()
cymk prog args curryImportPath
  | Help `elem` opts = printUsage prog
  | null errs = processFiles cymkOpts prog files
  | otherwise = badUsage prog errs
  where (opts,files,errs) = getOpt Permute options args
        cymkOpts =
	  foldr selectOption
                defaultOptions{ importPaths = map ((,) False) curryImportPath }
                opts

printUsage :: String -> IO ()
printUsage prog =
  do
    putStrLn (usageInfo (unlines header) options)
    exitWith (ExitSuccess)
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
  where script = buildScript (mkClean opts) (debug opts) (linkAlways opts)
			     (importPaths opts) (output opts)

putErr, putErrLn :: String -> IO ()
putErr = hPutStr stderr
putErrLn = hPutStr stderr . (++ "\n")
