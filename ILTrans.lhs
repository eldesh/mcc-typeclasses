% -*- LaTeX -*-
% $Id: ILTrans.lhs 3052 2011-10-05 19:25:15Z wlux $
%
% Copyright (c) 1999-2011, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{ILTrans.lhs}
\section{Translating Curry into the Intermediate Language}\label{sec:il-trans}
After desugaring and lifting have been performed, the source code is
translated into the intermediate language.

Because of name conflicts between the source and intermediate language
representations, we can only use a qualified import of the \texttt{IL}
module.
\begin{verbatim}

> module ILTrans(ilTrans) where
> import Base
> import Curry
> import CurryUtils
> import Env
> import qualified IL
> import List
> import Maybe
> import PredefTypes
> import Set
> import TopEnv
> import Types
> import TypeInfo
> import Utils
> import ValueInfo

\end{verbatim}
\paragraph{Modules}
At the top-level, the compiler has to translate data, type, function,
and foreign declarations. When translating data type and type synonym
declarations, we ignore the types in the declarations and look up the
types of the constructors in the type (constructor) environment
instead because these types are already fully expanded, i.e., they do
not include any alias types. Note that \texttt{ilTrans} first sorts
top-level declarations according to their textual order to ensure that
split annotations are inserted in IL code at the correct places.
\begin{verbatim}

> ilTrans :: TCEnv -> ValueEnv -> Module Type -> IL.Module
> ilTrans tcEnv tyEnv (Module m es _ ds) =
>   IL.Module m (exports es) (imports m ds') ds'
>   where ds' = concatMap (translTopDecl m tcEnv tyEnv) (sortDecls ds)
>         exports (Just (Exporting _ es)) =
>           filter (isJust . localIdent m) (concatMap values es)
>         values (Export x) = [x]
>         values (ExportTypeWith tc cs) = map (qualifyLike tc) cs

> translTopDecl :: ModuleIdent -> TCEnv -> ValueEnv -> TopDecl Type -> [IL.Decl]
> translTopDecl m _ tyEnv (DataDecl _ _ tc tvs cs _) =
>   [translData m tyEnv tc tvs cs]
> translTopDecl m tcEnv _ (TypeDecl _ tc _ _) = [translAlias m tcEnv tc]
> translTopDecl m _ tyEnv (BlockDecl d) = translDecl m tyEnv d
> translTopDecl _ _ _ (SplitAnnot _) = [IL.SplitAnnot]

> translDecl :: ModuleIdent -> ValueEnv -> Decl Type -> [IL.Decl]
> translDecl m tyEnv (FunctionDecl _ ty _ eqs) =
>   map (translFunction m tyEnv ty) eqs
> translDecl m _ (ForeignDecl _ fi ty f _) = [translForeign m f fi ty]
> translDecl _ _ _ = []

> translData :: ModuleIdent -> ValueEnv -> Ident -> [Ident] -> [ConstrDecl]
>            -> IL.Decl
> translData m tyEnv tc tvs cs =
>   IL.DataDecl (qualifyWith m tc) (length tvs)
>               (map (translConstrDecl m tyEnv) cs)

> translAlias :: ModuleIdent -> TCEnv -> Ident -> IL.Decl
> translAlias m tcEnv tc = IL.TypeDecl tc' n (translType ty)
>   where [AliasType tc' n _ ty] = qualLookupTopEnv (qualifyWith m tc) tcEnv

> translConstrDecl :: ModuleIdent -> ValueEnv -> ConstrDecl -> IL.ConstrDecl
> translConstrDecl m tyEnv d = IL.ConstrDecl c (map translType (arrowArgs ty))
>   where c = qualifyWith m (constr d)
>         ty = rawType (thd3 (conType c tyEnv))

> translForeign :: ModuleIdent -> Ident -> ForeignImport -> Type -> IL.Decl
> translForeign m f (cc,_,ie) ty =
>   IL.ForeignDecl (qualifyWith m f) (callConv cc) (fromJust ie) (translType ty)
>   where callConv CallConvPrimitive = IL.Primitive
>         callConv CallConvCCall = IL.CCall
>         callConv CallConvRawCall = IL.RawCall

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
intermediate language. Recall that every function has only a single
equation and all arguments are variables at this point.
\begin{verbatim}

> translFunction :: ModuleIdent -> ValueEnv -> Type -> Equation Type -> IL.Decl
> translFunction m tyEnv ty (Equation _ (FunLhs f ts) rhs) =
>   IL.FunctionDecl (qualifyWith m f) vs (translType ty)
>                   (translRhs tyEnv vs rhs)
>   where vs = [v | VariablePattern _ v <- ts]

> translRhs :: ValueEnv -> [Ident] -> Rhs Type -> IL.Expression
> translRhs tyEnv vs (SimpleRhs p e _) =
>   IL.SrcLoc (show p) (translExpr tyEnv vs e)

\end{verbatim}
\paragraph{Patterns}
Since pattern matching has been transformed already, patterns can be
translated almost directly into the intermediate language. The only
complication arises from as-patterns, which are not supported in the
intermediate language. Therefore, we return the respective variables
along with the transformed patterns.
\begin{verbatim}

> translLiteral :: Type -> Literal -> IL.Literal
> translLiteral _ (Char c) = IL.Char c
> translLiteral ty (Integer i) = translInt ty i
>   where translInt (TypeConstrained tys _) = translInt (head tys)
>         translInt ty
>           | ty == intType = IL.Int
>           | ty == integerType = IL.Integer
>           | otherwise = internalError ("translLiteral(Integer): " ++ show ty)
> translLiteral ty (Rational r) = translRat ty r
>   where translRat (TypeConstrained tys _) = translRat (head tys)
>         translRat ty
>           | ty == floatType = IL.Float . fromRational
>           | otherwise = internalError ("translLiteral(Rational): " ++ show ty)

> translTerm :: ConstrTerm Type -> ([Ident],IL.ConstrTerm)
> translTerm (LiteralPattern ty l) = ([],IL.LiteralPattern (translLiteral ty l))
> translTerm (VariablePattern _ v) = ([],IL.VariablePattern v)
> translTerm (ConstructorPattern _ c ts) =
>   ([],IL.ConstructorPattern c [v | VariablePattern _ v <- ts])
> translTerm (AsPattern v t) = (v:vs,t')
>   where (vs,t') = translTerm t

\end{verbatim}
\paragraph{Expressions}
The translation of expressions from lifted Curry source code into the
intermediate language is also almost straightforward. The only
exception are case expressions with alternatives using as-patterns.
Such expressions are transformed into an outer, flexible case
expression that evaluates the scrutinized expression and binds the
as-pattern variable,\footnote{Recall that case expressions in the
intermediate language always evaluate the scrutinized expression.}
and an inner case expression that matches this variable against the
actual pattern. We always use a flexible match for the outer case
expression because the compiler would generate a redundant switch
statement during the translation of the intermediate language into
abstract machine code otherwise.
\begin{verbatim}

> translExpr :: ValueEnv -> [Ident] -> Expression Type -> IL.Expression
> translExpr _ _ (Literal ty l) = IL.Literal (translLiteral ty l)
> translExpr tyEnv vs (Variable _ v)
>   | not (isQualified v) && v' `elem` vs = IL.Variable v'
>   | otherwise = IL.Function v (arity v tyEnv)
>   where v' = unqualify v
> translExpr tyEnv _ (Constructor _ c) = IL.Constructor c (arity c tyEnv)
> translExpr tyEnv vs (Apply e1 e2) =
>   IL.Apply (translExpr tyEnv vs e1) (translExpr tyEnv vs e2)
> translExpr tyEnv vs (Let ds e) =
>   case ds of
>     [FreeDecl _ vs'] -> IL.Exist (bv vs') e'
>     [d] -> IL.Let (rec d) [translBinding vs' d] e'
>     _ -> IL.Let IL.Rec (map (translBinding vs') ds) e'
>   where e' = translExpr tyEnv vs' e
>         vs' = vs ++ bv ds
>         translBinding vs (PatternDecl _ (VariablePattern _ v) rhs) =
>           IL.Binding v (translRhs tyEnv vs rhs)
>         rec d
>           | any (`elem` bv d) (qfv (mkMIdent []) d) = IL.Rec
>           | otherwise = IL.NonRec
> translExpr tyEnv vs (Case e as) =
>   caseExpr IL.Rigid (translExpr tyEnv vs e) (nub (concat vss')) as'
>   where (vss',as') = unzip (map (translAlt tyEnv vs) as)
> translExpr tyEnv vs (Fcase e as) =
>   case e of
>     Let [FreeDecl _ [FreeVar _ v]] (Variable _ v')
>       | qualify v == v' && all isChoice as ->
>           IL.Choice [translRhs tyEnv vs rhs | Alt _ _ rhs <- as]
>     _ -> caseExpr IL.Flex (translExpr tyEnv vs e) (nub (concat vss')) as'
>   where (vss',as') = unzip (map (translAlt tyEnv vs) as)
>         isChoice (Alt _ t rhs) = all (`notElem` qfv (mkMIdent []) rhs) (bv t)

> translAlt :: ValueEnv -> [Ident] -> Alt Type -> ([Ident],IL.Alt)
> translAlt tyEnv vs (Alt _ t rhs) = (filter (`elem` fv e') vs',IL.Alt t' e')
>   where (vs',t') = translTerm t
>         e' = translRhs tyEnv (vs ++ bv t) rhs

> caseExpr :: IL.Eval -> IL.Expression -> [Ident] -> [IL.Alt] -> IL.Expression
> caseExpr ev e vs as =
>   case (e,vs) of
>     (IL.Variable v,_) -> match ev v (filter (v /=) vs) as
>     (_,[]) -> IL.Case ev e as
>     (_,v:vs) ->
>       IL.Case IL.Flex e [IL.Alt (IL.VariablePattern v) (match ev v vs as)]
>   where match ev v vs as =
>           IL.Let IL.NonRec [IL.Binding v' e | v' <- vs] (IL.Case ev e as)
>           where e = IL.Variable v

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
>   fv (IL.Case _ e as) = fv e ++ fv as
>   fv (IL.Choice es) = fv es
>   fv (IL.Exist vs e) = filter (`notElem` vs) (fv e)
>   fv (IL.Let rec bs e) =
>     fvBinds rec vs (fv es) ++ filter (`notElem` vs) (fv e)
>     where (vs,es) = unzip [(v,e) | IL.Binding v e <- bs]
>           fvBinds IL.NonRec _ = id
>           fvBinds IL.Rec vs = filter (`notElem` vs)
>   fv (IL.SrcLoc _ e) = fv e

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
>   modules IL.SplitAnnot = id

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
>   modules (IL.Choice es) = modules es
>   modules (IL.Exist _ e) = modules e
>   modules (IL.Let _ bs e) = modules bs . modules e
>   modules (IL.SrcLoc _ e) = modules e

> instance HasModule IL.Alt where
>   modules (IL.Alt t e) = modules t . modules e

> instance HasModule IL.Binding where
>   modules (IL.Binding _ e) = modules e

> instance HasModule QualIdent where
>   modules x = maybe id (:) $ fst $ splitQualIdent x

\end{verbatim}
