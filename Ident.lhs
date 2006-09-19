% -*- LaTeX -*-
% $Id: Ident.lhs 1885 2006-04-05 21:23:18Z wlux $
%
% Copyright (c) 1999-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Ident.lhs}
\section{Identifiers}
This module provides the implementation of identifiers and some
utility functions for identifiers, which are used at various places in
the compiler.

Identifiers comprise the name of the denoted entity and an \emph{id},
which can be used for renaming identifiers, e.g., in order to resolve
name conflicts between identifiers from different scopes. An
identifier with an \emph{id} $0$ is considered as not being renamed
and, hence, its \emph{id} will not be shown.

\ToDo{Probably we should use \texttt{Integer} for the \emph{id}s.}

Qualified identifiers may optionally be prefixed by a module
name. \textbf{The order of the cases \texttt{UnqualIdent} and
\texttt{QualIdent} is important. Some parts of the compiler rely on
the fact that all qualified identifiers are greater than any
unqualified identifier.}
\begin{verbatim}

> module Ident(Ident,QualIdent,ModuleIdent,
>              mkIdent,name,qualName,uniqueId,
>              renameIdent,unRenameIdent,isRenamed,
>              mkMIdent,moduleName,moduleQualifiers,isInfixOp,isQInfixOp,
>              qualify,qualifyWith,qualifyLike,qualQualify,isQualified,
>              unqualify,qualUnqualify,localIdent,splitQualIdent,
>              emptyMIdent,preludeMIdent,debugPreludeMIdent,
>              ptrMIdent,stablePtrMIdent,
>              anonId,unitId,boolId,charId,intId,floatId,listId,ioId,
>              ptrId,funPtrId,stablePtrId,
>              successId,trueId,falseId,nilId,consId,mainId,
>              tupleId,isTupleId,tupleArity,selectorId,isSelectorId,
>              minusId,fminusId,
>              qUnitId,qBoolId,qCharId,qIntId,qFloatId,qListId,qIOId,
>              qSuccessId,qPtrId,qFunPtrId,qStablePtrId,
>              qTrueId,qFalseId,qNilId,qConsId,
>              qTupleId,isQTupleId,qTupleArity,isQSelectorId) where
> import Char
> import List

> data Ident = Ident String Int deriving (Eq,Ord)
> data QualIdent = UnqualIdent Ident | QualIdent ModuleIdent Ident
>                  deriving (Eq,Ord)
> newtype ModuleIdent = ModuleIdent [String] deriving (Eq,Ord)

> instance Show Ident where
>   showsPrec _ (Ident x n)
>     | n == 0 = showString x
>     | otherwise = showString x . showChar '.' . shows n
> instance Show QualIdent where
>   showsPrec _ (UnqualIdent x) = shows x
>   showsPrec _ (QualIdent m x) = shows m . showChar '.' . shows x
> instance Show ModuleIdent where
>   showsPrec _ m = showString (moduleName m)

> mkIdent :: String -> Ident
> mkIdent x = Ident x 0

> name :: Ident -> String
> name (Ident x _) = x

> qualName :: QualIdent -> String
> qualName (UnqualIdent x) = name x
> qualName (QualIdent m x) = moduleName m ++ "." ++ name x

> uniqueId :: Ident -> Int
> uniqueId (Ident _ n) = n

> renameIdent :: Ident -> Int -> Ident
> renameIdent (Ident x _) n = Ident x n

> unRenameIdent :: Ident -> Ident
> unRenameIdent (Ident x _) = Ident x 0

> isRenamed :: Ident -> Bool
> isRenamed (Ident _ n) = n /= 0

> mkMIdent :: [String] -> ModuleIdent
> mkMIdent = ModuleIdent

> moduleName :: ModuleIdent -> String
> moduleName (ModuleIdent xs) = concat (intersperse "." xs)

> moduleQualifiers :: ModuleIdent -> [String]
> moduleQualifiers (ModuleIdent xs) = xs

> isInfixOp :: Ident -> Bool
> isInfixOp (Ident ('<':c:cs) _)=
>   last (c:cs) /= '>' || not (isAlphaNum c) && c `notElem` "_(["
> isInfixOp (Ident (c:_) _) = not (isAlphaNum c) && c `notElem` "_(["
> isInfixOp (Ident _ _) = False -- error "Zero-length identifier"

> isQInfixOp :: QualIdent -> Bool
> isQInfixOp (UnqualIdent x) = isInfixOp x
> isQInfixOp (QualIdent _ x) = isInfixOp x

\end{verbatim}
The functions \texttt{qualify} and \texttt{qualifyWith} convert an
unqualified identifier into a qualified identifier (without and with a
given module prefix, respectively).
\begin{verbatim}

> qualify :: Ident -> QualIdent
> qualify = UnqualIdent

> qualifyWith :: ModuleIdent -> Ident -> QualIdent
> qualifyWith = QualIdent

> qualifyLike :: QualIdent -> Ident -> QualIdent
> qualifyLike (UnqualIdent _) x = UnqualIdent x
> qualifyLike (QualIdent m _) x = QualIdent m x

> qualQualify :: ModuleIdent -> QualIdent -> QualIdent
> qualQualify m (UnqualIdent x) = QualIdent m x
> qualQualify _ x = x

> isQualified :: QualIdent -> Bool
> isQualified (UnqualIdent _) = False
> isQualified (QualIdent _ _) = True

> unqualify :: QualIdent -> Ident
> unqualify (UnqualIdent x) = x
> unqualify (QualIdent _ x) = x

> qualUnqualify :: ModuleIdent -> QualIdent -> QualIdent
> qualUnqualify m (UnqualIdent x) = UnqualIdent x
> qualUnqualify m (QualIdent m' x)
>   | m == m' = UnqualIdent x
>   | otherwise = QualIdent m' x

> localIdent :: ModuleIdent -> QualIdent -> Maybe Ident
> localIdent _ (UnqualIdent x) = Just x
> localIdent m (QualIdent m' x)
>   | m == m' = Just x
>   | otherwise = Nothing

> splitQualIdent :: QualIdent -> (Maybe ModuleIdent,Ident)
> splitQualIdent (UnqualIdent x) = (Nothing,x)
> splitQualIdent (QualIdent m x) = (Just m,x)

\end{verbatim}
A few identifiers a predefined here.
\begin{verbatim}

> emptyMIdent, preludeMIdent, debugPreludeMIdent :: ModuleIdent
> emptyMIdent        = ModuleIdent []
> preludeMIdent      = ModuleIdent ["Prelude"]
> debugPreludeMIdent = ModuleIdent ["DebugPrelude"]

> ptrMIdent, stablePtrMIdent :: ModuleIdent
> ptrMIdent       = ModuleIdent ["Ptr"]
> stablePtrMIdent = ModuleIdent ["StablePtr"]

> anonId :: Ident
> anonId = Ident "_" 0

> unitId, boolId, charId, intId, floatId, listId, ioId, successId :: Ident
> unitId    = Ident "()" 0
> boolId    = Ident "Bool" 0
> charId    = Ident "Char" 0
> intId     = Ident "Int" 0
> floatId   = Ident "Float" 0
> listId    = Ident "[]" 0
> ioId      = Ident "IO" 0
> successId = Ident "Success" 0

> ptrId, funPtrId, stablePtrId :: Ident
> ptrId       = Ident "Ptr" 0
> funPtrId    = Ident "FunPtr" 0
> stablePtrId = Ident "StablePtr" 0

> trueId, falseId, nilId, consId :: Ident
> trueId  = Ident "True" 0
> falseId = Ident "False" 0
> nilId   = Ident "[]" 0
> consId  = Ident ":" 0

> tupleId :: Int -> Ident
> tupleId n
>   | n >= 2 = Ident ("(" ++ replicate (n - 1) ',' ++ ")") 0
>   | otherwise = error "internal error: tupleId"

> isTupleId :: Ident -> Bool
> isTupleId x = n > 1 && x == tupleId n
>   where n = length (name x) - 1

> tupleArity :: Ident -> Int
> tupleArity x
>   | n > 1 && x == tupleId n = n
>   | otherwise = error "internal error: tupleArity"
>   where n = length (name x) - 1

> selectorId :: Int -> Ident
> selectorId n = Ident ("_#sel" ++ show n) 0

> isSelectorId :: Ident -> Bool
> isSelectorId x = any ("_#sel" `isPrefixOf`) (tails (name x))

> mainId, minusId, fminusId :: Ident
> mainId = Ident "main" 0
> minusId = Ident "-" 0
> fminusId = Ident "-." 0

> qUnitId, qNilId, qConsId, qListId :: QualIdent
> qUnitId = UnqualIdent unitId
> qListId = UnqualIdent listId
> qNilId  = UnqualIdent nilId
> qConsId = UnqualIdent consId

> qBoolId, qCharId, qIntId, qFloatId, qSuccessId, qIOId :: QualIdent
> qBoolId = QualIdent preludeMIdent boolId
> qCharId = QualIdent preludeMIdent charId
> qIntId = QualIdent preludeMIdent intId
> qFloatId = QualIdent preludeMIdent floatId
> qSuccessId = QualIdent preludeMIdent successId
> qIOId = QualIdent preludeMIdent ioId

> qPtrId, qFunPtrId, qStablePtrId :: QualIdent
> qPtrId = QualIdent ptrMIdent ptrId
> qFunPtrId = QualIdent ptrMIdent funPtrId
> qStablePtrId = QualIdent stablePtrMIdent stablePtrId

> qTrueId, qFalseId :: QualIdent
> qTrueId = QualIdent preludeMIdent trueId
> qFalseId = QualIdent preludeMIdent falseId

> qTupleId :: Int -> QualIdent
> qTupleId = UnqualIdent . tupleId

> isQTupleId :: QualIdent -> Bool
> isQTupleId = isTupleId . unqualify

> qTupleArity :: QualIdent -> Int
> qTupleArity = tupleArity . unqualify

> isQSelectorId :: QualIdent -> Bool
> isQSelectorId = isSelectorId . unqualify

\end{verbatim}
