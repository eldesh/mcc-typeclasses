% -*- LaTeX -*-
% $Id: PredefTypes.lhs 2505 2007-10-16 21:22:00Z wlux $
%
% Copyright (c) 2002-2007, Wolfgang Lux
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
> import PredefIdent
> import Types

> unitType,boolType,charType,intType,floatType,stringType,successType :: Type
> unitType = TypeConstructor qUnitId
> boolType = TypeConstructor qBoolId
> charType = TypeConstructor qCharId
> intType = TypeConstructor qIntId
> floatType = TypeConstructor qFloatId
> stringType = listType charType
> successType = TypeConstructor qSuccessId

> listType,ioType :: Type -> Type
> listType = TypeApply (TypeConstructor qListId)
> ioType = TypeApply (TypeConstructor qIOId)

> tupleType :: [Type] -> Type
> tupleType tys = foldl TypeApply (TypeConstructor (qTupleId (length tys))) tys

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
> numTypes = [intType,floatType]
> fracTypes = tail numTypes

\end{verbatim}
