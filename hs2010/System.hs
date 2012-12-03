module System(ExitCode(ExitSuccess,ExitFailure),
              getArgs,getProgName,getEnv,system,exitWith,exitFailure) where
import System.Environment
import System.Exit
import System.Process
