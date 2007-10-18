% -*- LaTeX -*-
% $Id: ILTrans.lhs 2513 2007-10-18 09:50:08Z wlux $
%
% Copyright (c) 1999-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{ILTrans.lhs}
\section{Translating Curry into the Intermediate Language}\label{sec:il-trans}
After desugaring and lifting have been performed, the source code is
translated into the intermediate language. Besides translating from
source terms and expressions into intermediate language terms and
expressions, this phase in particular implements the pattern matching
algorithm for equations.

Because of name conflicts between the source and intermediate language
representations, we can only use a qualified import of the \texttt{IL}
module.
\begin{verbatim}

> module ILTrans(ilTrans,ilTransIntf) where
> import Base
> import Curry
> import CurryUtils
> import Env
> import qualified IL
> import List
> import Maybe
> import PredefIdent
> import Set
> import Types
> import TypeTrans
> import Utils
> import ValueInfo

\end{verbatim}
\paragraph{Modules}
At the top-level, the compiler has to translate data type, newtype,
function, and foreign declarations. When translating data type and
newtype declarations, we ignore the types in the declarations and
look up the types of the constructors in the type environment instead
because these types are already fully expanded, i.e., they do not
include any alias types. On the other hand, we introduce new type
synonyms in place of newtype declarations (see Sect.~\ref{sec:IL}).
\begin{verbatim}

> ilTrans :: ValueEnv -> Module a -> IL.Module
> ilTrans tyEnv (Module m _ _ ds) = IL.Module m (imports m ds') ds'
>   where ds' = concatMap (translTopDecl m tyEnv) ds

> translTopDecl :: ModuleIdent -> ValueEnv -> TopDecl a -> [IL.Decl]
> translTopDecl m tyEnv (DataDecl _ _ tc tvs cs _) =
>   [translData m tyEnv tc tvs cs]
> translTopDecl m tyEnv (NewtypeDecl _ _ tc tvs nc _) =
>   translNewtype m tyEnv tc tvs nc
> translTopDecl _ _ (TypeDecl _ _ _ _) = []
> translTopDecl _ _ (ClassDecl _ _ _ _ _) = []
> translTopDecl _ _ (InstanceDecl _ _ _ _ _) = []
> translTopDecl _ _ (DefaultDecl _ _) = []
> translTopDecl m tyEnv (BlockDecl d) = translDecl m tyEnv d

> translDecl :: ModuleIdent -> ValueEnv -> Decl a -> [IL.Decl]
> translDecl m tyEnv (FunctionDecl _ f eqs) = [translFunction m tyEnv f eqs]
> translDecl m tyEnv (ForeignDecl _ cc _ ie f _) =
>   [translForeign m tyEnv f cc (fromJust ie)]
> translDecl _ _ _ = []

> translData :: ModuleIdent -> ValueEnv -> Ident -> [Ident] -> [ConstrDecl]
>            -> IL.Decl
> translData m tyEnv tc tvs cs =
>   IL.DataDecl (qualifyWith m tc) (length tvs)
>               (map (translConstrDecl m tyEnv) cs)

> translNewtype :: ModuleIdent -> ValueEnv -> Ident -> [Ident] -> NewConstrDecl
>               -> [IL.Decl]
> translNewtype m tyEnv tc tvs nc =
>   [IL.TypeDecl (qualifyWith m tc) (length tvs) (translType (argType ty)),
>    IL.FunctionDecl f [v] (translType ty) (IL.Variable v)]
>   where f = qualifyWith m (nconstr nc)
>         v = head (argNames (mkIdent ""))
>         ty = rawType (snd (conType f tyEnv))
>         argType (TypeArrow ty _) = ty

> translConstrDecl :: ModuleIdent -> ValueEnv -> ConstrDecl -> IL.ConstrDecl
> translConstrDecl m tyEnv d = IL.ConstrDecl c (map translType (arrowArgs ty))
>   where c = qualifyWith m (constr d)
>         ty = rawType (snd (conType c tyEnv))

> translForeign :: ModuleIdent -> ValueEnv -> Ident -> CallConv -> String
>               -> IL.Decl
> translForeign m tyEnv f cc ie =
>   IL.ForeignDecl (qualifyWith m f) (callConv cc) ie
>                  (translType (rawType (varType f tyEnv)))
>   where callConv CallConvPrimitive = IL.Primitive
>         callConv CallConvCCall = IL.CCall
>         callConv CallConvRawCall = IL.RawCall

\end{verbatim}
\paragraph{Interfaces}
In order to generate code, the compiler also needs to know the tags
and arities of all imported data constructors. For that reason, we
compile the data type declarations of all interfaces into the
intermediate language, too. In this case we do not look up the
types in the environment because the types in the interfaces are
already fully expanded. Note that we do not translate data types
which are imported into the interface from another module.
\begin{verbatim}

> ilTransIntf :: Interface -> [IL.Decl]
> ilTransIntf (Interface m _ ds) = foldr (translIntfDecl m) [] ds

> translIntfDecl :: ModuleIdent -> IDecl -> [IL.Decl] -> [IL.Decl]
> translIntfDecl m (IDataDecl _ _ tc _ tvs cs) ds
>   | not (isQualified tc) = translIntfData m (unqualify tc) tvs cs : ds
> translIntfDecl _ _ ds = ds

> translIntfData :: ModuleIdent -> Ident -> [Ident] -> [Maybe ConstrDecl]
>                -> IL.Decl
> translIntfData m tc tvs cs =
>   IL.DataDecl (qualifyWith m tc) (length tvs)
>               (map (maybe hiddenConstr (translIntfConstrDecl m tvs)) cs)
>   where hiddenConstr = IL.ConstrDecl qAnonId []
>         qAnonId = qualify anonId

> translIntfConstrDecl :: ModuleIdent -> [Ident] -> ConstrDecl -> IL.ConstrDecl
> translIntfConstrDecl m tvs (ConstrDecl _ _ _ c tys) =
>   IL.ConstrDecl (qualifyWith m c) (map translType (toTypes m tvs tys))
> translIntfConstrDecl m tvs (ConOpDecl _ _ _ ty1 op ty2) =
>   IL.ConstrDecl (qualifyWith m op) (map translType (toTypes m tvs [ty1,ty2]))

\end{verbatim}
\paragraph{Types}
In contrast to the internal type representation, the intermediate
language does not support types with higher order kinds. The type
transformation therefore has to transform all types to first order
terms. To that end, we assume the existence of a type synonym
\texttt{type @ f a = f a}. In addition, the type representation of the
intermediate language does not support constrained type variables and
skolem types. The former are fixed and the latter are replaced by
fresh type constructors.
\begin{verbatim}

> translType :: Type -> IL.Type
> translType ty = fromType ty []
>   where fromType (TypeConstructor tc) = IL.TypeConstructor tc
>         fromType (TypeVariable tv) = foldl appType (IL.TypeVariable tv)
>         fromType (TypeConstrained tys _) = fromType (head tys)
>         fromType (TypeSkolem k) =
>           foldl appType
>                 (IL.TypeConstructor (qualify (mkIdent ("_" ++ show k))) []) 
>         fromType (TypeApply ty1 ty2) = fromType ty1 . (translType ty2 :)
>         fromType (TypeArrow ty1 ty2) =
>           foldl appType (IL.TypeArrow (translType ty1) (translType ty2))
>         appType ty1 ty2 = IL.TypeConstructor (qualify (mkIdent "@")) [ty1,ty2]

\end{verbatim}
\paragraph{Functions}
Every function in the program is translated into a function of the
intermediate language. The arguments of the function are renamed such
that all variables occurring in the same position (in different
equations) have the same name. This is necessary in order to
facilitate the translation of pattern matching into \texttt{case}
expressions. We use the following simple convention here: The
outermost arguments of the function are named \texttt{\_1},
\texttt{\_2}, and so on from left to right. The names of inner
arguments are constructed by appending \texttt{\_1}, \texttt{\_2},
etc. from left to right to the name that would be assigned to a
variable occurring at the position of the constructor term.

Some special care is needed for the selector functions introduced by
the compiler in place of pattern bindings. In order to generate the
code for updating all pattern variables, the equality of names between
the pattern variables in the first argument of the selector function
and their repeated occurrences in the remaining arguments must be
preserved. This means that the second and following arguments of a
selector function have to be renamed according to the name mapping
computed for its first argument.
\begin{verbatim}

> type RenameEnv = Env Ident Ident

> translFunction :: ModuleIdent -> ValueEnv -> Ident -> [Equation a] -> IL.Decl
> translFunction m tyEnv f eqs =
>   IL.FunctionDecl (qualifyWith m f) vs (translType ty)
>                   (match IL.Flex vs (map (translEquation tyEnv vs vs'') eqs))
>   where ty = rawType (varType f tyEnv)
>         vs = if isSelectorId f then translArgs eqs vs' else vs'
>         (vs',vs'') = splitAt (arity eqs) (argNames (mkIdent ""))
>         arity (Equation _ (FunLhs _ ts) _ : _) = length ts

> translArgs :: [Equation a] -> [Ident] -> [Ident]
> translArgs [Equation _ (FunLhs _ (t:ts)) _] (v:_) =
>   v : map (translArg (bindRenameEnv v t emptyEnv)) ts
>   where translArg env (VariablePattern _ v) = fromJust (lookupEnv v env)

> translEquation :: ValueEnv -> [Ident] -> [Ident] -> Equation a
>                -> ([NestedTerm],IL.Expression)
> translEquation tyEnv vs vs' (Equation _ (FunLhs _ ts) rhs) =
>   (zipWith translTerm vs ts,
>    translRhs tyEnv vs' (foldr2 bindRenameEnv emptyEnv vs ts) rhs)

> translRhs :: ValueEnv -> [Ident] -> RenameEnv -> Rhs a -> IL.Expression
> translRhs tyEnv vs env (SimpleRhs _ e _) = translExpr tyEnv vs env e

\end{verbatim}
\paragraph{Pattern Matching}
The pattern matching code searches for the left-most inductive
argument position in the left hand sides of all rules defining an
equation. An inductive position is a position where all rules have a
constructor rooted term. If such a position is found, a \texttt{case}
expression is generated for the argument at that position. The
matching code is then computed recursively for all of the alternatives
independently. If no inductive position is found, the algorithm looks
for the left-most demanded argument position, i.e., a position where
at least one of the rules has a constructor rooted term. If such a
position is found, an \texttt{or} expression is generated with those
cases that have a variable at the argument position in one branch and
all other rules in the other branch. If there is no demanded position,
the pattern matching is finished and the compiler translates the right
hand sides of the remaining rules, eventually combining them using
\texttt{or} expressions.

Actually, the algorithm below combines the search for inductive and
demanded positions. The function \texttt{match} scans the argument
lists for the left-most demanded position. If this turns out to be
also an inductive position, the function \texttt{matchInductive} is
called in order to generate a \texttt{case} expression. Otherwise, the
function \texttt{optMatch} is called that tries to find an inductive
position in the remaining arguments. If one is found,
\texttt{matchInductive} is called, otherwise the function
\texttt{optMatch} uses the demanded argument position found by
\texttt{match}.
\begin{verbatim}

> data NestedTerm = NestedTerm IL.ConstrTerm [NestedTerm] deriving Show

> pattern (NestedTerm t _) = t
> arguments (NestedTerm _ ts) = ts

> translLiteral :: Literal -> IL.Literal
> translLiteral (Char c) = IL.Char c
> translLiteral (Int i) = IL.Int i
> translLiteral (Float f) = IL.Float f
> translLiteral _ = internalError "translLiteral"

> translTerm :: Ident -> ConstrTerm a -> NestedTerm
> translTerm _ (LiteralPattern _ l) =
>   NestedTerm (IL.LiteralPattern (translLiteral l)) []
> translTerm v (VariablePattern _ _) = NestedTerm (IL.VariablePattern v) []
> translTerm v (ConstructorPattern _ c ts) =
>   NestedTerm (IL.ConstructorPattern c (zipWith const vs ts))
>              (zipWith translTerm vs ts)
>   where vs = argNames v
> translTerm v (AsPattern _ t) = translTerm v t
> translTerm _ _ = internalError "translTerm"

> bindRenameEnv :: Ident -> ConstrTerm a -> RenameEnv -> RenameEnv
> bindRenameEnv _ (LiteralPattern _ _) env = env
> bindRenameEnv v (VariablePattern _ v') env = bindEnv v' v env
> bindRenameEnv v (ConstructorPattern _ _ ts) env =
>   foldr2 bindRenameEnv env (argNames v) ts
> bindRenameEnv v (AsPattern v' t) env = bindEnv v' v (bindRenameEnv v t env)
> bindRenameEnv _ _ env = internalError "bindRenameEnv"

> argNames :: Ident -> [Ident]
> argNames v = [mkIdent (prefix ++ show i) | i <- [1..]]
>   where prefix = name v ++ "_"

> type Match = ([NestedTerm],IL.Expression)
> type Match' = ([NestedTerm] -> [NestedTerm],[NestedTerm],IL.Expression)

> isDefaultPattern :: IL.ConstrTerm -> Bool
> isDefaultPattern (IL.VariablePattern _) = True
> isDefaultPattern _ = False

> isDefaultMatch :: (IL.ConstrTerm,a) -> Bool
> isDefaultMatch = isDefaultPattern . fst

> match :: IL.Eval -> [Ident] -> [Match] -> IL.Expression
> match _  []     alts = foldl1 IL.Or (map snd alts)
> match ev (v:vs) alts
>   | null vars = e1
>   | null nonVars = e2
>   | otherwise = optMatch ev (IL.Or e1 e2) (v:) vs (map skipArg alts)
>   where (vars,nonVars) = partition isDefaultMatch (map tagAlt alts)
>         e1 = matchInductive ev id v vs nonVars
>         e2 = match ev vs (map snd vars)
>         tagAlt (t:ts,e) = (pattern t,(arguments t ++ ts,e))
>         skipArg (t:ts,e) = ((t:),ts,e)

> optMatch :: IL.Eval -> IL.Expression -> ([Ident] -> [Ident]) -> [Ident]
>          -> [Match'] -> IL.Expression
> optMatch _  e _      []     _ = e
> optMatch ev e prefix (v:vs) alts
>   | null vars = matchInductive ev prefix v vs nonVars
>   | otherwise = optMatch ev e (prefix . (v:)) vs (map skipArg alts)
>   where (vars,nonVars) = partition isDefaultMatch (map tagAlt alts)
>         tagAlt (prefix,t:ts,e) = (pattern t,(prefix (arguments t ++ ts),e))
>         skipArg (prefix,t:ts,e) = (prefix . (t:),ts,e)

> matchInductive :: IL.Eval -> ([Ident] -> [Ident]) -> Ident -> [Ident]
>                -> [(IL.ConstrTerm,Match)] -> IL.Expression
> matchInductive ev prefix v vs alts =
>   IL.Case ev (IL.Variable v) (matchAlts ev prefix vs alts)

> matchAlts :: IL.Eval -> ([Ident] -> [Ident]) -> [Ident]
>           -> [(IL.ConstrTerm,Match)] -> [IL.Alt]
> matchAlts _  _      _  [] = []
> matchAlts ev prefix vs ((t,alt):alts) =
>   IL.Alt t (match ev (prefix (vars t ++ vs)) (alt : map snd same)) :
>   matchAlts ev prefix vs others
>   where (same,others) = partition ((t ==) . fst) alts 
>         vars (IL.ConstructorPattern _ vs) = vs
>         vars _ = []

\end{verbatim}
Note that pattern matching in case expressions has been performed in
the \texttt{Desugar} module already, where case expressions with
nested patterns were transformed into nested case expressions with
flat patterns.

\paragraph{Expressions}
The translation of expressions from desugared Curry source code into
the intermediate language is very straight forward. A minor
complication arises for the translation of as-patterns, which are not
supported in the intermediate language. They are transformed into an
outer, flexible case expression that evaluates the scrutinized
expression and binds the as-pattern variable,\footnote{Recall that
  case expressions in the intermediate language always evaluate the
  scrutinized expression.} and an inner case expression that matches
this variable against the actual pattern. We always use a flexible
match for the outer case expression because the compiler would
generate a redundant switch statement during the translation of the
intermediate language into abstract machine code otherwise.

We also replace applications of newtype constructors by their
arguments. This transformation was performed already during
desugaring, but $\eta$-expansion and optimization may introduce
further possibilities to apply this transformation.
\begin{verbatim}

> translExpr :: ValueEnv -> [Ident] -> RenameEnv -> Expression a
>            -> IL.Expression
> translExpr _ _ _ (Literal _ l) = IL.Literal (translLiteral l)
> translExpr tyEnv _ env (Variable _ v) =
>   case lookupVar v env of
>     Just v' -> IL.Variable v'
>     Nothing -> IL.Function v (arity v tyEnv)
>   where lookupVar v env
>           | isQualified v = Nothing
>           | otherwise = lookupEnv (unqualify v) env
> translExpr tyEnv _ _ (Constructor _ c)
>   | isNewtypeConstr tyEnv c = IL.Function c 1
>   | otherwise = IL.Constructor c (arity c tyEnv)
> translExpr tyEnv vs env (Apply e1 e2) =
>   case e1 of
>     Constructor _ c | isNewtypeConstr tyEnv c -> translExpr tyEnv vs env e2
>     _ -> IL.Apply (translExpr tyEnv vs env e1) (translExpr tyEnv vs env e2)
> translExpr tyEnv vs env (Let ds e) =
>   case ds of
>     [FreeDecl _ vs] -> foldr IL.Exist e' vs
>     [d] | all (`notElem` bv d) (qfv (mkMIdent []) d) ->
>       IL.Let (translBinding env' d) e'
>     _ -> IL.Letrec (map (translBinding env') ds) e'
>   where e' = translExpr tyEnv vs env' e
>         env' = foldr2 bindEnv env bvs bvs
>         bvs = bv ds
>         translBinding env (PatternDecl _ (VariablePattern _ v) rhs) =
>           IL.Binding v (translRhs tyEnv vs env rhs)
> translExpr tyEnv (v:vs) env (Case e alts) =
>   caseExpr (translExpr tyEnv vs env e) (map (translAlt tyEnv vs env v) alts)
>   where caseExpr e alts
>           | v `elem` fv alts =
>               IL.Case IL.Flex e
>                       [IL.Alt (IL.VariablePattern v)
>                               (IL.Case IL.Rigid (IL.Variable v) alts)]
>           | otherwise = IL.Case IL.Rigid e alts
> translExpr _ _ _ _ = internalError "translExpr"

> translAlt :: ValueEnv -> [Ident] -> RenameEnv -> Ident -> Alt a -> IL.Alt
> translAlt tyEnv vs env v (Alt _ t rhs) =
>   IL.Alt (pattern (translTerm v t))
>          (translRhs tyEnv vs (bindRenameEnv v t env) rhs)

> instance QuantExpr IL.ConstrTerm where
>   bv (IL.LiteralPattern _) = []
>   bv (IL.ConstructorPattern _ vs) = vs
>   bv (IL.VariablePattern v) = [v]

> instance Expr IL.Expression where
>   fv (IL.Literal _) = []
>   fv (IL.Variable v) = [v]
>   fv (IL.Function _ _) = []
>   fv (IL.Constructor _ _) = []
>   fv (IL.Apply e1 e2) = fv e1 ++ fv e2
>   fv (IL.Case _ e alts) = fv e ++ fv alts
>   fv (IL.Or e1 e2) = fv e1 ++ fv e2
>   fv (IL.Exist v e) = filter (/= v) (fv e)
>   fv (IL.Let (IL.Binding v e1) e2) = fv e1 ++ filter (/= v) (fv e2)
>   fv (IL.Letrec bds e) = filter (`notElem` vs) (fv es ++ fv e)
>     where (vs,es) = unzip [(v,e) | IL.Binding v e <- bds]

> instance Expr IL.Alt where
>   fv (IL.Alt t e) = filterBv t (fv e)

\end{verbatim}
\paragraph{Auxiliary Definitions}
The list of import declarations in the intermediate language code is
determined by collecting all module qualifiers used in the current
module.
\begin{verbatim}

> imports :: ModuleIdent -> [IL.Decl] -> [ModuleIdent]
> imports m = toListSet . deleteFromSet m . fromListSet . flip modules []

> class HasModule a where
>   modules :: a -> [ModuleIdent] -> [ModuleIdent]

> instance HasModule a => HasModule [a] where
>   modules = flip (foldr modules)

> instance HasModule IL.Decl where
>   modules (IL.DataDecl _ _ cs) = modules cs
>   modules (IL.TypeDecl _ _ ty) = modules ty
>   modules (IL.FunctionDecl _ _ ty e) = modules ty . modules e
>   modules (IL.ForeignDecl _ _ _ ty) = modules ty

> instance HasModule IL.ConstrDecl where
>   modules (IL.ConstrDecl _ tys) = modules tys

> instance HasModule IL.Type where
>   modules (IL.TypeConstructor tc tys) = modules tc . modules tys
>   modules (IL.TypeVariable _) = id
>   modules (IL.TypeArrow ty1 ty2) = modules ty1 . modules ty2

> instance HasModule IL.ConstrTerm where
>   modules (IL.LiteralPattern _) = id
>   modules (IL.ConstructorPattern c _) = modules c
>   modules (IL.VariablePattern _) = id

> instance HasModule IL.Expression where
>   modules (IL.Literal _) = id
>   modules (IL.Variable _) = id
>   modules (IL.Function f _) = modules f
>   modules (IL.Constructor c _) = modules c
>   modules (IL.Apply e1 e2) = modules e1 . modules e2
>   modules (IL.Case _ e as) = modules e . modules as
>   modules (IL.Or e1 e2) = modules e1 . modules e2
>   modules (IL.Exist _ e) = modules e
>   modules (IL.Let b e) = modules b . modules e
>   modules (IL.Letrec bs e) = modules bs . modules e

> instance HasModule IL.Alt where
>   modules (IL.Alt t e) = modules t . modules e

> instance HasModule IL.Binding where
>   modules (IL.Binding _ e) = modules e

> instance HasModule QualIdent where
>   modules x = maybe id (:) $ fst $ splitQualIdent x

\end{verbatim}
