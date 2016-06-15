-- $Id: cycc.hs 3220 2016-06-15 22:32:30Z wlux $
--
-- Copyright (c) 1999-2015, Wolfgang Lux
-- See LICENSE for the full license.

import Combined
import Error
import Files
import GetOpt
import Goals
import IO
import List
import Maybe
import Modules
import Options
import System
import Utils

main :: IO ()
main =
  do
    prog <- getProgName
    args <- getArgs
    importPath <- getCurryImportPath
    cyc prog args importPath

cyc :: String -> [String] -> [ImportPath] -> IO ()
cyc prog args curryImportPath
  | Help `elem` opts = printUsage prog
  | null errs = processFiles cycOpts prog files
  | otherwise = badUsage prog errs
  where (opts,files,errs) = getOpt Permute options args
        cycOpts =
	  foldr selectOption
                defaultOptions{ importPaths = curryImportPath }
                opts

printUsage :: String -> IO ()
printUsage prog =
  do
    putStrLn (usageInfo (unlines header) options)
    exitWith ExitSuccess
  where header = ["usage: " ++ prog ++ " [OPTION]... SCRIPT..."]

badUsage :: String -> [String] -> IO ()
badUsage prog errs =
  do
    mapM_ (putErr . mkErrorLine) errs
    putErrLn ("Try `" ++ prog ++ " --help' for more information")
    exitWith (ExitFailure 1)
  where mkErrorLine err = prog ++ ": " ++ err

processFiles :: Options -> String -> [String] -> IO ()
processFiles opts prog files =
  case typeIt opts of
    Just g
      | isJust (goal opts) ->
          badUsage prog ["only one of -e and -t must be specified\n"]
      | otherwise -> compile (typeGoal opts g files)
    Nothing ->
      case goal opts of
        Just g
          | isNothing (output opts) ->
              badUsage prog ["must specify -e with an output file\n"]
          | otherwise -> compile (compileGoal opts g files)
	Nothing
          | null files -> badUsage prog ["no input files\n"]
          | isJust (output opts) && length files > 1 ->
              badUsage prog ["cannot specify -o with multiple input files\n"]
          | otherwise -> mapM_ (compile . compileModule opts) files

compile :: ErrorT IO a -> IO a
compile c = callErr c >>= checkOk
  where checkOk (Ok x) = return x
        checkOk (Errors msgs) =
          putErr (unlines (nub msgs)) >> exitWith (ExitFailure 1)
