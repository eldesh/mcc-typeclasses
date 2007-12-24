
-- Prelude to be included  (automatically) in all the programs
-- transformed for debugging purposes
-- Rafa 03-07-2001

module DebugPrelude(CTree(..),startDebugging,startIODebugging,clean,dEval,
                    try',return',bind',bind_',catch',fixIO',encapsulate',
                    unsafePerformIO',performIO,return,(>>=),(>>)) where
import Prelude hiding(Monad(..))
import IO

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
clean []         = []
clean ((p,x):xs) = if p=="_" 
		   then clean xs
		   else case x of
                        CTreeVoid  -> rest
		   	EmptyCTreeNode trees -> trees ++ rest
                        CTreeNode _ _ _ _ _ -> x : rest
		    where 
			 rest = clean xs
		

try' :: (a -> (Success,CTree)) -> ([a -> (Success,CTree)], CTree)
try' g = (map wrap (try (unwrap g)), CTreeVoid)

unwrap g (x,t) = case g x of (r,t') | r -> t =:= t'
wrap   g x | g (x,t) = (success,t) where t free


type IOT a = IO (a, CTree)

return' :: a -> IOT a
return' x = return (x, CTreeVoid)

bind' :: IOT a -> (a -> (IOT b, CTree)) -> IOT b
m `bind'` f =
  m >>= \(x,t1) ->
  case f x of
    (m',t2) ->
      m' >>= \(y,t3) ->
      return (y, EmptyCTreeNode (clean [(dEval x,t1),(dEval m',t2),(dEval y,t3)]))

bind_' :: IOT a -> IOT b -> IOT b
m1 `bind_'` m2 =
  m1 >>= \(x,t1) ->
  m2 >>= \(y,t2) ->
  return (y, EmptyCTreeNode (clean [(dEval x,t1),(dEval y,t2)]))

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
encapsulate' :: a -> IOT (a -> (Success, CTree))
encapsulate' e = encapsulate e >>= \g -> return' (\x -> (g x, CTreeVoid))
  where foreign import primitive encapsulate :: a -> IO (a -> Success)

foreign import primitive "unsafePerformIO" unsafePerformIO' :: IOT a -> (a, CTree)


startDebugging :: (a -> (Success,CTree)) -> IO ()
startDebugging = navigate . map snd . findall . unwrap

startIODebugging :: IOT a -> IO ()
startIODebugging goal = goal >>= \(_,t) -> navigate [t]

performIO :: (IOT a, CTree) -> IOT a
performIO (m,t1) = m >>= \(r,t2) -> return (r, ioCTree t1 (r,t2))

ioCTree :: CTree -> (a,CTree) -> CTree
ioCTree CTreeVoid (r,t) = EmptyCTreeNode (clean [(dEval r,t)])
ioCTree (EmptyCTreeNode trees) (r,t) =
  EmptyCTreeNode (trees ++ clean [(dEval r,t)])
ioCTree (CTreeNode name args _ rule trees) (r,t) =
  CTreeNode name args ("return " ++ dEval r) rule (trees ++ clean [(dEval r,t)])


-- rhs=debugging for navigating, rhs=prettyTree for pretty printing
data Answer = Yes | No | GoBack | Quit

navigate trees =
	do
	     putStrLn "" 
             putStrLn "Entering debugger..." 
	     navigateAux trees

navigateAux []  =
	do
             putStrLn "" 
             putStrLn "No error has been found"
             putStrLn "Debugger exiting" 
navigateAux (CTreeVoid : other) = navigateAux other
navigateAux (CTreeNode _ _ _ _ trees : other) = debugging trees other
navigateAux (EmptyCTreeNode trees : other) = debugging trees other

debugging trees other =
	do
             bugFound <- buggyChildren trees
             case bugFound of
                Yes    ->
	     	   do
		      putStrLn ""
		      putStrLn "Debugger exiting" 
                No     -> navigateAux other
		GoBack ->
		   do
		      putStrLn ""
		      putStrLn "Cannot go back to previous solution"
		      debugging trees other
                Quit   ->
	     	   do
		      putStrLn ""
		      putStrLn "Debugger exiting" 


buggyTree CTreeVoid = return No
buggyTree (EmptyCTreeNode trees) = buggyChildren trees
buggyTree n@(CTreeNode name args result rule trees) = 
        do
             putStrLn ""
             b <- buggyChildren trees
             case b of
                Yes    -> return Yes  
                No     ->
		   do
		      putStrLn (isBuggy n)
		      putStrLn ""
		      putStrLn "Buggy node found"
		      putStr   "Continue debugging? [y(es)/n(o)/b(ack)/q(uit)] "
		      hFlush stdout
		      yes <- answerYes
		      case yes of
			 Yes    -> if null trees then return GoBack else buggyTree n
			 No     -> return Yes
			 GoBack -> return GoBack
			 Quit   -> return Quit
    	        GoBack -> return GoBack
                Quit   -> return Quit

basicArrow (CTreeNode name args result rule trees) =
    name++concatMap (' ':) args++"  -> "++result



isBuggy (CTreeNode name args result rule trees) = 
	" ** Function "++name++" is incorrect **\n" ++
	(if null rule then "" else " Error is at " ++ rule ++ "\n") ++
        " Wrong instance: " ++	basicArrow (CTreeNode name args result rule trees)

buggyChildren [] = return No
buggyChildren (x:xs) = 
	do
	putStrLn ""
	putStrLn ("Considering the following basic fact" ++ (if null xs	then "" else "s") ++ ":")
	mapIO putStrLn listArrows
	putStr ((if null xs then "Is this" else "Are all of them") ++ " valid? [y(es)/n(o)/b(ack)/q(uit)] ")
        hFlush stdout
    	yes <- answerYes
        case yes of
           Yes -> putStrLn "" >> return No
           No ->
	      do
	         n <- chooseOne l
		 b <- buggyTree ((x:xs)!!(n-1))
		 case b of
		    GoBack -> putStrLn "" >> buggyChildren (x:xs)
		    _      -> return b
 	   GoBack -> return GoBack
           Quit   -> return Quit

 where 
	l = length (x:xs)
	listN = zip [1..l]  (x:xs)
	listArrows = map (\(x,y) -> shows x (". "++basicArrow y)) listN
	   
answerYes = 
  getLine >>= \l ->
  if l=="y" || l=="Y" then return Yes
  else if l=="n" || l=="N" then return No
  else if l=="b" || l=="B" then return GoBack
  else if l=="q" || l=="Q" then return Quit
  else putStr "[y(es)/n(o)/b(ack)/q(uit)] " >> hFlush stdout >> answerYes

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
-- Pretty (not really) Printing of the computation trees
--

prettyTree:: CTree -> IO ()
prettyTree = ppCTs 0
 
ppCTs :: Int -> CTree -> IO ()
ppCTs i CTreeVoid =	putStrLn "DebugPrelude.CTreeVoid"
	
ppCTs i (EmptyCTreeNode trees) = 
	do 
	   ident i
	   ppTChildren i trees
	   putStrLn ""

ppCTs i (CTreeNode name args result rule trees) = 
	do 
	   ident i
	   putStr "CTreeNode " 
	   putStr (name++" ")
	   putStr ("["++(concat (map (" "++) args))++"] ")
	   putStr  (result++" ")
	   putStr rule
	   ppTChildren i trees
	   putStrLn ""

ident n = putStr (take n (repeat ' '))

ppTChildren i []  = putStr "[]"
ppTChildren i (x:xs)  = 
	do
	   putStrLn ""
	   ident (i+2)
	   putStrLn "["
	   mapIO (ppCTs (i+3)) (x:xs)
   	   ident (i+2)
   	   putStrLn "]"

dEval:: a -> String
dEval x = dvals x ""
