% -*- LaTeX -*-
% $Id: IdentInfo.lhs 2724 2008-06-14 16:42:57Z wlux $
%
% Copyright (c) 1999-2008, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{IdentInfo.lhs}
\section{Type and Value Identifiers}
In order to implement syntax checking, we use two environments that
map type and value identifiers on their kinds.
\begin{verbatim}

> module IdentInfo where
> import Curry
> import CurryUtils
> import List
> import NestEnv
> import Set
> import TopEnv

\end{verbatim}
\subsection{Type Identifiers}
At the type level, we distinguish data and renaming types, synonym
types, and type classes. Type variables are not recorded. Type
synonyms use a kind of their own so that the compiler can verify that
no type synonyms are used in type expressions in interface files. The
initial type identifier environment \texttt{initTEnv} is empty.
\begin{verbatim}

> type TypeEnv = TopEnv TypeKind
> data TypeKind =
>     Data QualIdent [Ident]
>   | Alias QualIdent
>   | Class QualIdent [Ident]
>   deriving Show

> instance Entity TypeKind where
>   origName (Data tc _) = tc
>   origName (Alias tc) = tc
>   origName (Class cls _) = cls
>   merge (Data tc1 cs1) (Data tc2 cs2)
>     | tc1 == tc2 = Just (Data tc1 (cs1 `union` cs2))
>     | otherwise = Nothing
>   merge (Data _ _) (Alias _) = Nothing
>   merge (Data _ _) (Class _ _) = Nothing
>   merge (Alias _) (Data _ _) = Nothing
>   merge (Alias tc1) (Alias tc2)
>     | tc1 == tc2 = Just (Alias tc1)
>     | otherwise = Nothing
>   merge (Alias _) (Class _ _) = Nothing
>   merge (Class _ _) (Data _ _) = Nothing
>   merge (Class _ _) (Alias _) = Nothing
>   merge (Class cls1 fs1) (Class cls2 fs2)
>     | cls1 == cls2 = Just (Class cls1 (fs1 `union` fs2))
>     | otherwise = Nothing

> initTEnv :: TypeEnv
> initTEnv = emptyTopEnv

\end{verbatim}
The function \texttt{tidents} returns the type kind of the type
constructor or type class identifier declared by an interface
declaration, if any. Note that hiding data type and class declarations
are ignored deliberately, they must be changed into standard data type
declarations with \texttt{CurryUtils.unhide} before applying
\texttt{tidents} when necessary.
\begin{verbatim}

> tidents :: IDecl -> [TypeKind]
> tidents (IInfixDecl _ _ _ _) = []
> tidents (HidingDataDecl _ _ _ _) = []
> tidents (IDataDecl _ _ tc _ _ cs xs') = [Data tc (filter (`notElem` xs') xs)]
>   where xs = map constr cs ++ nub (concatMap labels cs)
> tidents (INewtypeDecl _ _ tc _ _ nc xs') =
>   [Data tc (filter (`notElem` xs') xs)]
>   where xs = nconstr nc : nlabel nc
> tidents (ITypeDecl _ tc _ _ _) = [Alias tc]
> tidents (HidingClassDecl _ _ _ _ _) = []
> tidents (IClassDecl _ _ cls _ _ ds fs) =
>   [Class cls (filter (`notElem` fs) (map imethod ds))]
> tidents (IInstanceDecl _ _ _ _ _) = []
> tidents (IFunctionDecl _ _ _ _) = []

\end{verbatim}
\subsection{Instances}
When checking for duplicate instance declarations, the compiler uses a
set of $C$-$T$ pairs, which contains one element for each defined or
imported instance. Instances are recorded only for the original names
of the type class and type constructor involved. The initial instance
set \texttt{instISet} is empty.
\begin{verbatim}

> data CT = CT QualIdent QualIdent deriving (Eq,Ord,Show)
> type InstSet = Set CT

> initISet :: InstSet
> initISet = zeroSet

\end{verbatim}
\subsection{Value Identifiers}
At pattern and expression level, we distinguish constructors on one
side and functions (including type class methods) and variables on the
other side. Field labels are represented as variables here, too. Each
variable has an associated list of identifiers, which contains the
names of all constructors for which the variable is also a valid field
label. We use the original names of the constructors because the
import paths of the constructors and labels are not relevant.

Since scopes can be nested in source code, we use a nested environment
for checking source modules and goals, whereas a flat top-level
environment is sufficient for checking import and export declarations.
The initial value identifier environment \texttt{initVEnv} is empty.
\begin{verbatim}

> type FunEnv = TopEnv ValueKind
> type VarEnv = NestEnv ValueKind

> data ValueKind =
>     Constr QualIdent
>   | Var QualIdent [QualIdent]
>   deriving Show

> instance Entity ValueKind where
>   origName (Constr c) = c
>   origName (Var x _) = x
>   merge (Constr c1) (Constr c2)
>     | c1 == c2 = Just (Constr c1)
>     | otherwise = Nothing
>   merge (Constr _) (Var _ _) = Nothing
>   merge (Var _ _) (Constr _) = Nothing
>   merge (Var v1 cs1) (Var v2 cs2)
>     | v1 == v2 = Just (Var v1 (cs1 `union` cs2))
>     | otherwise = Nothing

> initVEnv :: FunEnv
> initVEnv = emptyTopEnv

\end{verbatim}
The function \texttt{vidents} returns the value kinds of the value
identifiers declared by an interface declaration.
\begin{verbatim}

> vidents :: IDecl -> [ValueKind]
> vidents (IInfixDecl _ _ _ _) = []
> vidents (HidingDataDecl _ _ _ _) = []
> vidents (IDataDecl _ _ tc _ _ cs xs) =
>   cidents tc xs (map constr cs) ++
>   lidents tc xs [(l,constrs cs l) | l <- nub (concatMap labels cs)]
>   where constrs cs l = [constr c | c <- cs, l `elem` labels c]
> vidents (INewtypeDecl _ _ tc _ _ nc xs) =
>   cidents tc xs [nconstr nc] ++
>   lidents tc xs [(l,[c]) | NewRecordDecl _ c l _ <- [nc]]
> vidents (ITypeDecl _ _ _ _ _) = []
> vidents (HidingClassDecl _ _ _ _ _) = []
> vidents (IClassDecl _ _ cls _ _ ds fs) = midents cls fs (map imethod ds)
> vidents (IInstanceDecl _ _ _ _ _) = []
> vidents (IFunctionDecl _ f _ _) = [Var f []]

> cidents :: QualIdent -> [Ident] -> [Ident] -> [ValueKind]
> cidents tc xs cs = [Constr (qualifyLike tc c) | c <- cs, c `notElem` xs]

> lidents :: QualIdent -> [Ident] -> [(Ident,[Ident])] -> [ValueKind]
> lidents tc xs ls = [lident l cs | (l,cs) <- ls, l `notElem` xs]
>   where lident l cs = Var (qualifyLike tc l) (map (qualifyLike tc) cs)

> midents :: QualIdent -> [Ident] -> [Ident] -> [ValueKind]
> midents cls fs' fs = [Var (qualifyLike cls f) [] | f <- fs, f `notElem` fs']

\end{verbatim}
