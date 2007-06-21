
-- Prelude to be included  (automatically) in all the programs
-- transformed for debugging purposes
-- Rafa 03-07-2001

module DebugPrelude(CTree(..),startDebugging,startIODebugging,clean,dEval,
                    try',return',bind',bind_',catch',fixIO',encapsulate') where
import IO

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
		

-- 08-05-02 Try defined for debugging
try' :: (a -> (Success,CTree)) -> [a -> (Success,CTree)]
try' g = map wrap (try (unwrap g))


unwrap   g (x,t) | r = t =:= t' where (r,t') = g x 
wrap     g x | g (x,t) = (success,t) where t free


type IOT a = IO (a, CTree)

return' :: a -> IOT a
return' x = return (x, CTreeVoid)

bind' :: IOT a -> (a -> (IOT b, CTree)) -> IOT b
m `bind'` f =
  do
    (x,t1) <- m
    case f x of
      (m',t2) ->
        do
          (y,t3) <- m'
          return (y, EmptyCTreeNode (clean [(dEval x,t1),(dEval m',t2),(dEval y,t3)]))

bind_' :: IOT a -> IOT b -> IOT b
m1 `bind_'` m2 =
  do
    (x,t1) <- m1
    (y,t2) <- m2
    return (y, EmptyCTreeNode (clean [(dEval x,t1),(dEval y,t2)]))

catch' :: IOT a -> (IOError -> (IOT a, CTree)) -> IOT a
catch' m f = catch m (wrap f)
  where wrap f ioe =
          case f ioe of
            (m,t1) ->
              do
                (x,t2) <- m
                return (x, EmptyCTreeNode (clean [(dEval m,t1),(dEval x,t2)]))

-- NB It is important that wrap uses a lazy pattern; otherwise, the result
--    of the (transformed) recursive IO action would be requested before it
--    even had a chance to produce (a prefix of) it.
fixIO' :: (a -> (IOT a, CTree)) -> IOT a
fixIO' f = fixIO (wrap f)
  where foreign import primitive fixIO :: (a -> IO a) -> IO a
        wrap f ~(x,_) =
          case f x of
            (m,t1) ->
              do
                (y,t2) <- m
                return (y, EmptyCTreeNode (clean [(dEval m,t1),(dEval y,t2)]))

-- NB The computation tree CTreeVoid associated with the application f x
--    means one cannot detect any bugs in expression e (at least as far
--    as e is evaluated within the encapsulated search). Unfortunately,
--    there is nothing we can do about that. Encapsulate creates an
--    independent copy of its argument, which includes all computation
--    trees created locally during e's evaluation.
encapsulate' :: a -> IOT (a -> (Success, CTree))
encapsulate' e =
  do
    g <- encapsulate e
    return' (\x -> (g x, CTreeVoid))
  where foreign import primitive encapsulate :: a -> IO (a -> Success)


startDebugging :: ((a, CTree) -> Success) -> IO ()
startDebugging = navigate . map snd . findall

startIODebugging :: (IOT a, CTree) -> IO ()
startIODebugging (m, CTreeNode name args result rule trees) =
  do
    (x,t) <- m
    navigate [CTreeNode name args result rule (trees ++ clean [(dEval x,t)])]


-- rhs=debugging for navigating, rhs=prettyTree for pretty printing
data Answer = Yes | No | Abort

navigate trees =
	do
	     putStrLn "" 
             putStrLn "Entering debugger..." 
	     debugging trees

debugging []  =
	do
             putStrLn "" 
             putStrLn "No error has been found"
             putStrLn "Debugger exiting" 
debugging (CTreeNode name args result rule trees : other) = 
	do
             bugFound <- buggyChildren trees
             putStrLn "" 
             case bugFound of
                Yes   ->
	     	   do
		      putStrLn "Buggy node found"
		      putStrLn "Debugger exiting" 
                No    -> debugging other
                Abort -> debugging []

             
buggyTree CTreeVoid = return No
buggyTree (EmptyCTreeNode trees) = buggyChildren trees
buggyTree n@(CTreeNode name args result rule trees) = 
        do
             b <- buggyChildren trees
             case b of
                Yes   -> return Yes  
                No    -> putStrLn "" >> putStrLn (isBuggy n) >> return Yes
                Abort -> return Abort
    	          

basicArrow (CTreeNode name args result rule trees) =
    name++concatMap (' ':) args++"  -> "++result



isBuggy (CTreeNode name args result rule trees) = 
	" ** Function "++name++" is incorrect **\n" ++
        " Wrong instance: " ++	basicArrow (CTreeNode name args result rule trees)

buggyChildren [] = return No
buggyChildren (x:xs) = 
	do
	putStrLn ""
	putStrLn ("Considering the following basic fact" ++ (if null xs	then "" else "s") ++ ":")
	mapIO putStrLn listArrows
	putStr ((if null xs then "Is this" else "Are all of them") ++ " valid? [y(es)/n(o)/a(bort)] ")
        hFlush stdout
    	yes <- answerYes
        case yes of
           Yes -> return No
           No
             | null xs -> putStrLn "" >> buggyTree x
             | otherwise -> chooseOne l >>= \n -> putStrLn "" >> buggyTree ((x:xs)!!(n-1))
           Abort -> return Abort
 	 
 where 
	l = length (x:xs)
	listN = zip [1..l]  (x:xs)
	listArrows = map (\(x,y) -> shows x (". "++basicArrow y)) listN
	   
answerYes = 
  getLine >>= \l -> if l=="y" || l=="Y" then return Yes
                     else  if l=="n" || l=="N" then return No
                           else if l=="a" || l =="A" then return Abort
                                else putStr "[y(es)/n(o)/a(bort)] " >>
                                     hFlush stdout >>
                                     answerYes

chooseOne max =
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
