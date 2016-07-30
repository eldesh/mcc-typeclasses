-- $Id: DebugPrelude.curry 3292 2016-07-30 12:55:31Z wlux $
--
-- Copyright (c) 2007-2016, Wolfgang Lux
-- See ../LICENSE for the full license.
--
-- Prelude to be included  (automatically) in all the programs
-- transformed for debugging purposes
-- Rafa 03-07-2001

module DebugPrelude(CTree(..),startDebugging,startIODebugging,clean,dEval,
                    try',return',bind',bind_',catch',fixIO',encapsulate',
                    unsafePerformIO',performIO,return,(>>=),(>>)) where
import Prelude hiding(Monad(..))
import Ptr
import IO

infixl 1 >>, >>=

foreign import primitive return :: a -> IO a
foreign import primitive (>>=) :: IO a -> (a -> IO b) -> IO b
foreign import primitive (>>)  :: IO a -> IO b -> IO b
foreign import primitive dvals :: a -> ShowS

-- data type representing computation trees		   	
data CTree = CTreeNode String [String] String String [CTree] | 
             EmptyCTreeNode [CTree] | CTreeVoid


-- This function removes all the trees corresponding to non-demanded values
-- It not only saves time and space but it is neccessary for avoiding 
-- non terminating computations
clean :: [(String,CTree)] -> [CTree]
clean = flatten . prune

prune []         = []
prune ((p,x):xs) = if p=="_" then prune xs else x : prune xs

flatten []     = []
flatten (x:xs) =
  case x of
    CTreeVoid            -> flatten xs
    EmptyCTreeNode trees -> trees ++ flatten xs
    CTreeNode _ _ _ _ _  -> x : flatten xs


try' :: (a -> (Bool,CTree)) -> ([a -> (Bool,CTree)], CTree)
try' g = (map wrap (try (unwrap g)), CTreeVoid)

unwrap g (x,t) = case g x of (r,t') | r -> t =:= t'
wrap   g x | g (x,t) = (True,t) where t free


type IOT a = IO (a, CTree)

return' :: a -> IOT a
return' x = return (x, CTreeVoid)

bind' :: IOT a -> (a -> (IOT b, CTree)) -> IOT b
m `bind'` f =
  m >>= \(x,t1) ->
  case f x of
    (m',t2) ->
      m' >>= \(y,t3) ->
      return (y, EmptyCTreeNode (flatten [t1,t2,t3]))

bind_' :: IOT a -> IOT b -> IOT b
m1 `bind_'` m2 =
  m1 >>= \(x,t1) ->
  m2 >>= \(y,t2) ->
  return (y, EmptyCTreeNode (flatten [t1,t2]))

catch' :: IOT a -> (IOError -> (IOT a, CTree)) -> IOT a
catch' m f = catch m (wrap f)
  where wrap f ioe = performIO (f ioe)

-- NB It is important that wrap uses a lazy pattern; otherwise, the result
--    of the (transformed) recursive IO action would be requested before it
--    even had a chance to produce (a prefix of) it.
fixIO' :: (a -> (IOT a, CTree)) -> IOT a
fixIO' f = fixIO (wrap f)
  where foreign import primitive fixIO :: (a -> IO a) -> IO a
        wrap f xt = performIO (f (fst xt))

-- NB The computation tree CTreeVoid associated with the application f x
--    means one cannot detect any bugs in expression e (at least as far
--    as e is evaluated within the encapsulated search). Unfortunately,
--    there is nothing we can do about that. Encapsulate creates an
--    independent copy of its argument, which includes all computation
--    trees created locally during e's evaluation.
encapsulate' :: a -> IOT (a -> (Bool, CTree))
encapsulate' e = encapsulate e >>= \g -> return' (\x -> (g x, CTreeVoid))
  where foreign import primitive encapsulate :: a -> IO (a -> Bool)

foreign import primitive "unsafePerformIO" unsafePerformIO' :: IOT a -> (a, CTree)


startDebugging :: (a -> (Bool,CTree)) -> IO ()
startDebugging = navigate . findall . unwrap

startIODebugging :: IOT a -> IO ()
startIODebugging goal = goal >>= navigateAux . snd

performIO :: (IOT a, CTree) -> IOT a
performIO (m,t1) = m >>= \(r,t2) -> return (r, ioCTree t1 (r,t2))

ioCTree :: CTree -> (a,CTree) -> CTree
ioCTree CTreeVoid (_,t) = EmptyCTreeNode (flatten [t])
ioCTree (EmptyCTreeNode trees) (_,t) =
  EmptyCTreeNode (trees ++ flatten [t])
ioCTree (CTreeNode name args _ rule trees) (r,t) =
  CTreeNode name args ("return " ++ dEval r) rule (trees ++ flatten [t])


data Answer = Yes | No | Back | Quit

navigate [] = putStrLn "No more solutions"
navigate ((r,t) : other) =
	do
	     putStrLn (dEval r)
	     yes <- answerYes "Debug solution? "
	     case yes of
	       Yes  -> navigateAux t
	       No   -> navigate other
	       Back ->
		   do
		      putStrLn "Cannot go back to previous solution"
		      navigate ((r,t) : other)
	       Quit -> return ()

-- rhs=debugging for navigating, rhs=prettyTree for pretty printing
navigateAux = debugging

debugging tree =
  do
    dumpCTree <- getEnv "DUMP_CTREE"
    if null dumpCTree
      then
	do
	     putStrLn ""
             putStrLn "Entering debugger..."
	     debuggingAux (children tree)
	     putStrLn ""
	     putStrLn "Debugger exiting"
      else
        writeFile dumpCTree (xmlTree tree)

debuggingAux trees =
	do
             bugFound <- buggyChildren trees
             case bugFound of
                Yes  -> return ()
                No   -> putStrLn "No error has been found"
		Back ->
		   do
		      putStrLn ""
		      putStrLn "Cannot go back further (root of tree)"
		      debuggingAux trees
                Quit -> return ()

children CTreeVoid = []
children (EmptyCTreeNode trees) = trees
children (CTreeNode _ _ _ _ trees) = trees


buggyTree n@(CTreeNode name args result rule trees) =
        do
             putStrLn ""
             b <- buggyChildren trees
             case b of
                Yes  -> return True
                No   ->
		   do
		      putStrLn (isBuggy n)
		      putStrLn ""
		      putStrLn "Buggy node found"
		      yes <- answerYes "Continue debugging? "
		      case yes of
			 Yes  -> if null trees then return False else buggyTree n
			 No   -> return True
			 Back -> return False
			 Quit -> return True
    	        Back -> return False
                Quit -> return True

basicArrow (CTreeNode name args result rule trees) =
    arrowHead name args++"  -> "++result

arrowHead name args
  | isOp name =
      case args of
        [arg1,arg2] -> arg1 ++ ' ' : name ++ ' ' : arg2
	_ -> '(' : name ++ ')' : concatMap (' ':) args
  | otherwise = name ++ concatMap (' ':) args
  where isOp cs = maybeOp False cs
        maybeOp isOp cs =
	  case dropWhile ('.'/=) cs of
	    "" -> isOp
	    "." -> True
	    '.':c:cs'
	      | isDigit c && all isDigit cs' -> isOp
	      | isAlpha c -> maybeOp False cs'
	      | otherwise -> maybeOp True (c:cs')
	isAlpha c = c >= 'A' && c <= 'Z' || c >= 'a' && c <= 'z' || c == '_'
	isDigit c = c >= '0' && c <= '9'



isBuggy (CTreeNode name args result rule trees) = 
	" ** Function "++name++" is incorrect **\n" ++
	(if null rule then "" else " Error is at " ++ rule ++ "\n") ++
        " Wrong instance: " ++	basicArrow (CTreeNode name args result rule trees)

buggyChildren [] = return No
buggyChildren (x:xs) =
	do
	putStrLn ""
	putStrLn ("Considering the following basic fact" ++ (if null xs	then "" else "s") ++ ":")
	mapIO putStrLn (zipWith (\x y -> shows x (". "++basicArrow y)) [1..] (x:xs))
    	yes <- answerYes ((if null xs then "Is this" else "Are all of them") ++ " valid? ")
        case yes of
           Yes  -> putStrLn "" >> return No
           No   ->
	      do
	         n <- chooseOne (length (x:xs))
		 b <- buggyTree ((x:xs)!!(n-1))
		 if b then return Yes else putStrLn "" >> buggyChildren (x:xs)
 	   Back -> return Back
           Quit -> return Quit


answerYes prompt =
  putStr (prompt ++ "[y(es)/n(o)/b(ack)/q(uit)] ") >>
  hFlush stdout >> getLine >>= \l ->
  if l=="y" || l=="Y" then return Yes
  else if l=="n" || l=="N" then return No
  else if l=="b" || l=="B" then return Back
  else if l=="q" || l=="Q" then return Quit
  else answerYes ""

chooseOne max =
	if max <= 1 then return max else
 	do
 	 putStrLn "Write the number of an erroneous basic fact in the list "
	 n <- getLine
	 let valueN  = foldl (\x y->x*10+(ord(y)-ord('0'))) 0 n in
	  if valueN<1 || valueN>max then chooseOne max
        	                     else return valueN

----------------------------------------------------------------------------

--
-- Create XML representation of the computation tree
--

xmlTree :: CTree -> String
xmlTree tree = xmlProlog ++ xmlDoctype ++ xmlCTree tree ""

xmlProlog = "<?xml version='1.0'?>\n"

xmlDoctype =
  "<!DOCTYPE cTree [\n\
  \<!ELEMENT cTree (function*)>\n\
  \<!ATTLIST cTree version CDATA '1.0'>\n\
  \<!ELEMENT function (argument*,result,function*)>\n\
  \<!ATTLIST function name CDATA #REQUIRED srcLoc CDATA #IMPLIED>\n\
  \<!ELEMENT argument (#PCDATA)>\n\
  \<!ELEMENT result (#PCDATA)>\n\
  \]>\n"

xmlCTree tree =
  xmlElement "cTree" [] $ showChar '\n' . xmlFunctions (children tree)

xmlFunctions trees = flip (foldr xmlFunction) (flatten trees)

xmlFunction (CTreeNode name args result rule trees) =
  xmlElement "function" [("name",name),("srcLoc",rule)] $
  showChar '\n' .
  flip (foldr (xmlElement "argument" [] . xmlPCData)) args .
  xmlElement "result" [] (xmlPCData result) .
  xmlFunctions trees

xmlElement tag attrs element =
  showString ('<' : tag) . flip (foldr showAttr) attrs . showChar '>' .
  element . showString ("</" ++ tag ++ ">\n")
  where showAttr (key,val) =
  	  showChar ' ' . showString key . showChar '=' . xmlCData val

xmlCData cs = showChar '\'' . showString (quoteXML entities cs) . showChar '\''
  where entities = [('<',"&lt;"),('>',"&gt;"),('&',"&amp;"),('\'',"&apos;")]

xmlPCData = showString . quoteXML [('<',"&lt;"),('>',"&gt;"),('&',"&amp;")]

quoteXML entities = foldr quote ""
  where quote c = maybe (c:) (++) (lookup c entities)

----------------------------------------------------------------------------

--
-- Pretty (not really) Printing of the computation trees
--

prettyTree:: CTree -> IO ()
prettyTree = ppCTs 0
 
ppCTs :: Int -> CTree -> IO ()
ppCTs i CTreeVoid =	putStrLn "DebugPrelude.CTreeVoid"
	
ppCTs i (EmptyCTreeNode trees) = 
	do 
	   indent i
	   ppTChildren i trees
	   putStrLn ""

ppCTs i (CTreeNode name args result rule trees) = 
	do 
	   indent i
	   putStr "CTreeNode " 
	   putStr (name++" ")
	   putStr ("["++(concat (map (" "++) args))++"] ")
	   putStr  (result++" ")
	   putStr rule
	   ppTChildren i trees
	   putStrLn ""

indent n = putStr (take n (repeat ' '))

ppTChildren i []  = putStr "[]"
ppTChildren i (x:xs)  = 
	do
	   putStrLn ""
	   indent (i+2)
	   putStrLn "["
	   mapIO (ppCTs (i+3)) (x:xs)
   	   indent (i+2)
   	   putStrLn "]"

dEval:: a -> String
dEval x = dvals x ""


----------------------------------------------------------------------------

-- NB getEnv (re)defined here so that DebugPrelude can be compiled
--    without the standard library. Also note that this implementation
--    returns an empty string if the environment variable is not set
--    whereas System.getEnv raises an IO exception.
getEnv :: String -> IO String
getEnv var =
  do
    p1 <- primNewCString $## var
    p2 <- getenv p1
    mfree p1
    if p2 == nullPtr then return "" else primPeekCString p2
  where foreign import rawcall "cstring.h"
  		       primNewCString :: String -> IO (Ptr Char)
        foreign import rawcall "cstring.h"
		       primPeekCString :: Ptr Char -> IO String
        foreign import ccall "stdlib.h" getenv :: Ptr Char -> IO (Ptr Char)
        foreign import ccall "stdlib.h free" mfree :: Ptr a -> IO ()
