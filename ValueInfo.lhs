% -*- LaTeX -*-
% $Id: ValueInfo.lhs 2692 2008-05-02 13:22:41Z wlux $
%
% Copyright (c) 1999-2008, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{ValueInfo.lhs}
\section{Function and Constructor Types}
The compiler maintains information about the types of all data
constructors, functions, and variables in the module. For the purpose
of type checking, there is no need to distinguish variables and
functions. For all entities, their original names and their types are
saved. In addition, the compiler also saves the (optional) list of
field labels for data and newtype constructors and the arity of
functions. The length of the list of field labels of a data
constructor is always equal to the constructor's arity. If a data or
newtype constructor was declared without field labels, an anonymous
identifier is used in place of each of the labels. Additional
information is recorded for data constructors, which is explained
below.

Even though value declarations may be nested, the compiler uses a flat
environment for saving type information. This is possible because all
identifiers are renamed by the compiler before it starts computing type
information.
\begin{verbatim}

> module ValueInfo where
> import Base
> import Ident
> import TopEnv
> import Types

> type ValueEnv = TopEnv ValueInfo
> data ValueInfo = DataConstructor QualIdent [Ident] ConstrInfo TypeScheme
>                | NewtypeConstructor QualIdent Ident TypeScheme
>                | Value QualIdent Int TypeScheme
>                deriving Show

> instance Entity ValueInfo where
>   origName (DataConstructor c _ _ _) = c
>   origName (NewtypeConstructor c _ _) = c
>   origName (Value x _ _) = x

\end{verbatim}
The initial value type environment \texttt{initDCEnv} is empty.
\begin{verbatim}

> initDCEnv :: ValueEnv
> initDCEnv = emptyTopEnv

\end{verbatim}
The functions \texttt{bindFun} and \texttt{rebindFun} respectively add
and change the type of a function in the value type environment.
\begin{verbatim}

> bindFun :: ModuleIdent -> Ident -> Int -> TypeScheme -> ValueEnv -> ValueEnv
> bindFun m f n ty = bindTopEnv m f (Value (qualifyWith m f) n ty)

> rebindFun :: ModuleIdent -> Ident -> Int -> TypeScheme -> ValueEnv -> ValueEnv
> rebindFun m f n ty = rebindTopEnv m f (Value (qualifyWith m f) n ty)

\end{verbatim}
For a data constructor declaration
\begin{quote}\tt
  data $\textrm{\emph{cx}}_l$ => $T\,u_1 \dots u_n$ =
    \dots{} | forall $v_1 \dots v_{n'}$ .\ $\textrm{\emph{cx}}_r$ =>
    $C\,t_1 \dots t_k$ | \dots
\end{quote}
it is important to distinguish the left and right hand side contexts
$\emph{cx}_l$ and $\emph{cx}_r$. While instances for the constrained
types of the left hand side context $\emph{cx}_l$ must be available in
every context where $C$ is used, the right hand side context
$\emph{cx}_r$ introduces additional instances that are available
inside a context where $C$ is matched. Operationally, this means that
a dictionary argument is added to $C$ for each element of the context
$\emph{cx}_r$ (and therefore must be provided when $C$ is applied).
Since $C$'s type is
\begin{displaymath}
\forall u_1 \dots u_n \, v_1 \dots v_{n'}.\;\emph{cx} \Rightarrow
t_1 \rightarrow \dots \rightarrow t_k \rightarrow T\,u_1 \dots u_n
\end{displaymath}
where $cx$ is the concatenation of $\emph{cx}_l$ and $\emph{cx}_r$
restricted to the type variables that appear in $t_1,\dots,t_k$, it is
sufficient to record $\emph{cx}_r$ in addition to the constructor's
type. We also record the number of existentially quantified type
variables $n'$ in the additional data constructor information because
it simplifies distinguishing universally and existentially quantified
type variables in $C$'s type.

The function \texttt{stdConstrInfo} returns the trivial data
constructor information for a data (or newtype) constructor that has
no existentially quantified type variables and whose right hand side
context is empty.
\begin{verbatim}

> data ConstrInfo = ConstrInfo Int Context deriving (Eq,Show)

> stdConstrInfo :: ConstrInfo
> stdConstrInfo = ConstrInfo 0 []

\end{verbatim}
The functions \texttt{conType}, \texttt{varType}, and \texttt{funType}
return the type of constructors, pattern variables, and variables in
expressions, respectively, from the type environment. They are
supposed to be used only after checking for duplicate and ambiguous
identifiers and therefore should not fail.

The function \texttt{conType} also returns the list of field labels
and the additional information associated with the constructor.

The function \texttt{varType} can handle ambiguous identifiers and
returns the first available type. This makes it possible to use
\texttt{varType} in order to determine the type of a locally defined
function even when the function's name is ambiguous.
\begin{verbatim}

> conType :: QualIdent -> ValueEnv -> ([Ident],ConstrInfo,TypeScheme)
> conType c tyEnv =
>   case qualLookupTopEnv c tyEnv of
>     [DataConstructor _ ls ci ty] -> (ls,ci,ty)
>     [NewtypeConstructor _ l ty] -> ([l],stdConstrInfo,ty)
>     _ -> internalError ("conType " ++ show c)

> varType :: Ident -> ValueEnv -> TypeScheme
> varType v tyEnv =
>   case lookupTopEnv v tyEnv of
>     Value _ _ ty : _ -> ty
>     _ -> internalError ("varType " ++ show v)

> funType :: QualIdent -> ValueEnv -> TypeScheme
> funType f tyEnv =
>   case qualLookupTopEnv f tyEnv of
>     [Value _ _ ty] -> ty
>     _ -> internalError ("funType " ++ show f)

\end{verbatim}
The function \texttt{arity} returns the arity of a constructor or
function and the function \texttt{changeArity} changes the arity of a
(local) function.
\begin{verbatim}

> arity :: QualIdent -> ValueEnv -> Int
> arity x tyEnv =
>   case qualLookupTopEnv x tyEnv of
>     [DataConstructor _ ls _ _] -> length ls
>     [NewtypeConstructor _ _ _] -> 1
>     [Value _ n _] -> n
>     _ -> internalError ("arity " ++ show x)

> changeArity :: ModuleIdent -> Ident -> Int -> ValueEnv -> ValueEnv
> changeArity m f n tyEnv =
>   case lookupTopEnv f tyEnv of
>     Value _ n' ty : _ -> if n /= n' then rebindFun m f n ty tyEnv else tyEnv
>     _ -> internalError ("changeArity " ++ show f)

\end{verbatim}
The function \texttt{isNewtypeConstr} uses the value type environment
in order to distinguish data and newtype constructors.
\begin{verbatim}

> isNewtypeConstr :: ValueEnv -> QualIdent -> Bool
> isNewtypeConstr tyEnv c =
>   case qualLookupTopEnv c tyEnv of
>     [DataConstructor _ _ _ _] -> False
>     [NewtypeConstructor _ _ _] -> True
>     _ -> internalError ("isNewtypeConstr: " ++ show c)

\end{verbatim}
