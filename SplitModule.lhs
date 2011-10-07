% -*- LaTeX -*-
% $Id: SplitModule.lhs 3056 2011-10-07 16:27:03Z wlux $
%
% Copyright (c) 2011, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{SplitModule.lhs}
\section{Splitting Modules}
In order to reduce the size of executables statically linked against
the standard library and also to avoid passing huge source files to
the C compiler, the compiler can automatically split a module into
several independent compilation units. Our splitting strategy computes
minimal mutually recursive declaration groups for the (intermediate
language) code of a module and emits one compilation unit for each
group containing at least one exported definition. A separate
compilation unit is also created for each group that is used by two or
more other compilation units. Private declaration groups used by only
one other compilation unit are included in that unit. This strategy
minimizes the size of executables by allowing the linker to link in
only the minimal number of definitions used by a program and at the
same time allows us to keep private as many definitions as possible.
Note that in particular lifted local function definitions are always
included in the same compilation unit as their original top level
definition and are never going to be exported.

A special case is needed for the data type definitions of a module.
The debugging transformation does not rename data
constructors.\footnote{The reason for not renaming data constructors
  is that the runtime system is not able to detect transformed lists
  and tuples when displaying terms in basic facts and solutions and
  the required changes would impact performance of untransformed
  code.} To prevent name conflicts between transformed and
untransformed code of the standard library we generate a compilation
unit for each data type definition and export all constructors when
compiling without the debugging transformation and discard the data
type definitions altogether when compiling with the debugging
transformation. Thus, no name conflicts can occur for programs
compiled for debugging that are linked with the transformed standard
library \emph{and} the untransformed library. The latter is needed by
the small top level program that controls the debugger at runtime.

Note that no special treatment is necessary for foreign function
declarations even though they are not renamed by the debugging
transformation either. However, foreign functions are used only by
their wrappers in transformed code. Since
they are also not exported from the transformed module, foreign
function declarations end up as private declarations in the same
compilation unit as their wrappers.
\begin{verbatim}

> module SplitModule(splitModule) where
> import IL
> import List
> import SCC

> infixr 5 +++

> data Group a = Group{ defd::[QualIdent], used::[QualIdent], decls::[a] }

> splitModule :: Bool -> Module -> [Module]
> splitModule debug (Module m es is ds) =
>   concat [map (mkDataModule m is) cs | not debug] ++
>   zipWith (mkModule m is) (tail xss) dss
>   where (cs,fs) = partition isDataDecl (filter (not . null . defs) ds)
>         dss = foldr (addGroup es . join) [] (scc defd used (map group fs))
>         xss = scanr (++) [] (map used dss ++ [es])
>         group d = Group{ defd = defs d, used = funs d, decls = [d] }
>         isDataDecl (DataDecl _ _ _) = True
>         isDataDecl (FunctionDecl _ _ _ _) = False
>         isDataDecl (ForeignDecl _ _ _ _) = False

> mkModule :: ModuleIdent -> [ModuleIdent] -> [QualIdent] -> Group Decl
>          -> Module
> mkModule m is xs Group{ defd=fs, decls=ds } =
>   Module m (filter (`elem` xs) fs) is ds

> mkDataModule :: ModuleIdent -> [ModuleIdent] -> Decl -> Module
> mkDataModule m is d = Module m (constrs d) is [d]
>   where constrs (DataDecl _ _ cs) = [c | ConstrDecl c _ <- cs]

> addGroup :: [QualIdent] -> Group a -> [Group a] -> [Group a]
> addGroup es ds@Group{ defd=xs } dss
>   | any (`elem` es) xs = ds : dss
>   | otherwise =
>       case findIndices (\xs' -> any (`elem` xs') xs) (map used dss) of
>         [] ->  dss
>         [i] -> dss' ++ (ds +++ ds') : dss''
>           where (dss',ds':dss'') = splitAt i dss
>         _ -> ds : dss

> (+++) :: Group a -> Group a -> Group a
> Group xs1 ys1 ds1 +++ ~(Group xs2 ys2 ds2) =
>   Group (xs1 ++ xs2) (ys1 ++ ys2) (ds1 ++ ds2)

> join :: [Group a] -> Group a
> join ds = foldr (+++) Group{ defd=[], used=[], decls=[] } ds

\end{verbatim}
The following functions compute the lists of defined values and used
functions, respectively, for a given declaration.
\begin{verbatim}

> defs :: Decl -> [QualIdent]
> defs (DataDecl _ _ cs) = [c | ConstrDecl c _ <- cs]
> defs (TypeDecl _ _ _) = []
> defs (FunctionDecl f _ _ _) = [f]
> defs (ForeignDecl f _ _ _) = [f]

> funs :: Decl -> [QualIdent]
> funs (DataDecl _ _ _) = []
> funs (TypeDecl _ _ _) = []
> funs (FunctionDecl _ _ _ e) = usedFuns e []
> funs (ForeignDecl _ _ _ _) = []

> class Expr a where
>   usedFuns :: a -> [QualIdent] -> [QualIdent]

> instance Expr a => Expr [a] where
>   usedFuns es xs = foldr usedFuns xs es

> instance Expr ConstrTerm where
>   usedFuns (LiteralPattern _) = id
>   usedFuns (ConstructorPattern c _) = (c :)
>   usedFuns (VariablePattern _) = id

> instance Expr Expression where
>   usedFuns (Literal _) = id
>   usedFuns (Variable _) = id
>   usedFuns (Function f _) = (f :)
>   usedFuns (Constructor c _) = id
>   usedFuns (Apply e1 e2) = usedFuns e1 . usedFuns e2
>   usedFuns (Case _ e as) = usedFuns e . usedFuns as
>   usedFuns (Choice es) = usedFuns es
>   usedFuns (Exist _ e) = usedFuns e
>   usedFuns (Let _ ds e) = usedFuns ds . usedFuns e
>   usedFuns (SrcLoc _ e) = usedFuns e

> instance Expr Alt where
>   usedFuns (Alt t e) = usedFuns t . usedFuns e

> instance Expr Binding where
>   usedFuns (Binding _ e) = usedFuns e

\end{verbatim}
