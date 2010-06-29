% -*- LaTeX -*-
% $Id: PredefTypes.lhs 2969 2010-06-29 13:00:29Z wlux $
%
% Copyright (c) 2002-2010, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{PredefTypes.lhs}
\section{Predefined Types}
This module defines the predefined types that are known to the
compiler.
\begin{verbatim}

> module PredefTypes where
> import Ident
> import PredefIdent
> import Types

> unitType,boolType,charType,intType,integerType,floatType,rationalType :: Type
> stringType,successType :: Type
> unitType = TypeConstructor qUnitId
> boolType = TypeConstructor qBoolId
> charType = TypeConstructor qCharId
> intType = TypeConstructor qIntId
> integerType = TypeConstructor qIntegerId
> floatType = TypeConstructor qFloatId
> rationalType = ratioType integerType
> stringType = listType charType
> successType = TypeConstructor qSuccessId

> listType,ioType,ratioType :: Type -> Type
> listType = TypeApply (TypeConstructor qListId)
> ioType = TypeApply (TypeConstructor qIOId)
> ratioType = TypeApply (TypeConstructor qRatioId)

> tupleType :: [Type] -> Type
> tupleType tys = foldl TypeApply (TypeConstructor (qTupleId (length tys))) tys

> qualUnitType,qualBoolType,qualCharType,qualIntType,qualIntegerType :: QualType
> qualFloatType,qualRationalType :: QualType
> qualUnitType = QualType [] unitType
> qualBoolType = QualType [] boolType
> qualCharType = QualType [] charType
> qualIntType = QualType [] intType
> qualIntegerType = QualType [] integerType
> qualFloatType = QualType [] floatType
> qualRationalType = qualRatioType qualIntegerType
> qualStringType = qualListType qualCharType
> qualSuccessType = QualType [] successType

> qualListType,qualIOType,qualRatioType :: QualType -> QualType
> qualListType (QualType cx ty) = QualType cx (listType ty)
> qualIOType (QualType cx ty) = QualType cx (ioType ty)
> qualRatioType (QualType cx ty) = QualType cx (ratioType ty)

\end{verbatim}
The variable \texttt{guardTypes} maintains the list of types
admissible for guard expressions. The first type of this list
(\texttt{Success}), is used as default type if the guard's type cannot
be determined otherwise.
\begin{verbatim}

> guardTypes :: [Type]
> guardTypes = [successType,boolType]

\end{verbatim}
The variables \texttt{numTypes} and \texttt{fracTypes} maintain the
lists of types admissible for ambiguous types with \texttt{Num} and
\texttt{Fractional} constraints, respectively.
\begin{verbatim}

> numTypes, fracTypes :: [Type]
> numTypes = [intType,integerType,floatType]
> fracTypes = drop 2 numTypes

\end{verbatim}
