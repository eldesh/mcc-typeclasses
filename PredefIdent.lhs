% -*- LaTeX -*-
% $Id: PredefIdent.lhs 2692 2008-05-02 13:22:41Z wlux $
%
% Copyright (c) 1999-2008, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{PredefIdent.lhs}
\section{Predefined Identifiers}
This module defines predefined identifiers used at various places in
the compiler.

The function \texttt{lambdaId} returns the canonical name of a lambda
abstraction, which is based on its position in the source code. The
function \texttt{selectorId} returns the name of an auxiliary function
that is used to extract components of a pattern in a pattern
declaration (see p.~\pageref{pattern-binding} in
Sect.~\ref{sec:simplify}).
\begin{verbatim}

> module PredefIdent where
> import Ident
> import List
> import Position

> preludeMIdent, debugPreludeMIdent, ratioMIdent :: ModuleIdent
> ptrMIdent, stablePtrMIdent :: ModuleIdent
> preludeMIdent      = mkMIdent ["Prelude"]
> debugPreludeMIdent = mkMIdent ["DebugPrelude"]
> ratioMIdent        = mkMIdent ["Ratio"]
> ptrMIdent          = mkMIdent ["Ptr"]
> stablePtrMIdent    = mkMIdent ["StablePtr"]

> lambdaId :: Position -> Ident
> lambdaId (Position _ l c) =
>   mkIdent ("_#lambda_line_" ++ show l ++ '.' : show c)

> unitId, nilId, consId, listId, arrowId :: Ident
> unitId  = mkIdent "()"
> nilId   = mkIdent "[]"
> consId  = mkIdent ":"
> listId  = mkIdent "[]"
> arrowId = mkIdent "->"

> tupleId :: Int -> Ident
> tupleId n
>   | n >= 2 = mkIdent ("(" ++ replicate (n - 1) ',' ++ ")")
>   | otherwise = error "internal error: tupleId"

> isTupleId :: Ident -> Bool
> isTupleId x = n > 1 && x == tupleId n
>   where n = length (name x) - 1

> tupleArity :: Ident -> Int
> tupleArity x
>   | n > 1 && x == tupleId n = n
>   | otherwise = error "internal error: tupleArity"
>   where n = length (name x) - 1

> boolId, charId, intId, integerId, floatId, ratioId, ioId, successId :: Ident
> boolId    = mkIdent "Bool"
> charId    = mkIdent "Char"
> intId     = mkIdent "Int"
> integerId = mkIdent "Integer"
> floatId   = mkIdent "Float"
> ratioId   = mkIdent "Ratio"
> ioId      = mkIdent "IO"
> successId = mkIdent "Success"

> eqId, ordId, enumId, boundedId, showId, numId, fractionalId, monadId :: Ident
> eqId         = mkIdent "Eq"
> ordId        = mkIdent "Ord"
> enumId       = mkIdent "Enum"
> boundedId    = mkIdent "Bounded"
> showId       = mkIdent "Show"
> numId        = mkIdent "Num"
> fractionalId = mkIdent "Fractional"
> monadId      = mkIdent "Monad"

> ptrId, funPtrId, stablePtrId :: Ident
> ptrId       = mkIdent "Ptr"
> funPtrId    = mkIdent "FunPtr"
> stablePtrId = mkIdent "StablePtr"

> trueId, falseId :: Ident
> trueId  = mkIdent "True"
> falseId = mkIdent "False"

> selectorId :: Int -> Ident
> selectorId n = mkIdent ("_#sel" ++ show n)

> isSelectorId :: Ident -> Bool
> isSelectorId x = any ("_#sel" `isPrefixOf`) (tails (name x))

> mainId, minusId :: Ident
> mainId = mkIdent "main"
> minusId = mkIdent "-"

> qUnitId, qNilId, qConsId, qListId, qArrowId :: QualIdent
> qUnitId  = qualifyWith preludeMIdent unitId
> qNilId   = qualifyWith preludeMIdent nilId
> qConsId  = qualifyWith preludeMIdent consId
> qListId  = qualifyWith preludeMIdent listId
> qArrowId = qualifyWith preludeMIdent arrowId

> qTupleId :: Int -> QualIdent
> qTupleId = qualifyWith preludeMIdent . tupleId

> isQTupleId :: QualIdent -> Bool
> isQTupleId = isTupleId . unqualify

> qTupleArity :: QualIdent -> Int
> qTupleArity = tupleArity . unqualify

> qBoolId, qCharId, qIntId, qIntegerId, qFloatId, qRatioId :: QualIdent
> qSuccessId, qIOId :: QualIdent
> qBoolId = qualifyWith preludeMIdent boolId
> qCharId = qualifyWith preludeMIdent charId
> qIntId = qualifyWith preludeMIdent intId
> qIntegerId = qualifyWith preludeMIdent integerId
> qFloatId = qualifyWith preludeMIdent floatId
> qRatioId = qualifyWith ratioMIdent ratioId
> qSuccessId = qualifyWith preludeMIdent successId
> qIOId = qualifyWith preludeMIdent ioId

> qEqId, qOrdId, qEnumId, qBoundedId, qShowId :: QualIdent
> qNumId, qFractionalId, qMonadId :: QualIdent
> qEqId = qualifyWith preludeMIdent eqId
> qOrdId = qualifyWith preludeMIdent ordId
> qEnumId = qualifyWith preludeMIdent enumId
> qBoundedId = qualifyWith preludeMIdent boundedId
> qShowId = qualifyWith preludeMIdent showId
> qNumId = qualifyWith preludeMIdent numId
> qFractionalId = qualifyWith preludeMIdent fractionalId
> qMonadId = qualifyWith preludeMIdent monadId

> qPtrId, qFunPtrId, qStablePtrId :: QualIdent
> qPtrId = qualifyWith ptrMIdent ptrId
> qFunPtrId = qualifyWith ptrMIdent funPtrId
> qStablePtrId = qualifyWith stablePtrMIdent stablePtrId

> qTrueId, qFalseId :: QualIdent
> qTrueId = qualifyWith preludeMIdent trueId
> qFalseId = qualifyWith preludeMIdent falseId

> isQSelectorId :: QualIdent -> Bool
> isQSelectorId = isSelectorId . unqualify

\end{verbatim}
The type and data constructors of the unit, list, and tuple types are
handled specially. These entities are defined in the Prelude but they
can be accessed only with special syntax and are available in every
module. The functions \texttt{isPrimTypeId} and\texttt{isPrimDataId}
can be used to check for the type and data constructor identifiers of
these types.
\begin{verbatim}

> isPrimTypeId :: Ident -> Bool
> isPrimTypeId tc = tc `elem` [unitId,listId,arrowId] || isTupleId tc

> isPrimDataId :: Ident -> Bool
> isPrimDataId c = c `elem` [unitId,nilId,consId] || isTupleId c

\end{verbatim}
