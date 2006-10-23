% -*- LaTeX -*-
% $Id: Types.lhs 1981 2006-10-23 22:42:43Z wlux $
%
% Copyright (c) 2002-2006, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Types.lhs}
\section{Types}
This module provides the definitions for the internal representation
of types in the compiler.
\begin{verbatim}

> module Types where
> import Ident
> import List

\end{verbatim}
A type is either a type variable, an application of a type constructor
to a list of arguments, or an arrow type. The \texttt{TypeGuard} case
is used for typing a guard expression in a equation with only a single
guard, which can either have type \texttt{Bool} or \texttt{Success}.
\texttt{TypeGuard} variables allow delaying the decision for a fixed
type until the whole module has been checked. If the
\texttt{TypeGuard} variable is still not restricted, it will be
defaulted to type \texttt{Success}. The case \texttt{TypeSkolem} is
used for handling skolem types, which result from matching data
constructors with existentially quantified types.

Type variables are represented with deBruijn style indices. Universally
quantified type variables are assigned indices in the order of their
occurrence in the type from left to right. This leads to a canonical
representation of types where $\alpha$-equivalence of two types
coincides with equality of the representation.

Note that even though \texttt{TypeGuard} variables use indices as
well, these variables must never be quantified.
\begin{verbatim}

> data Type =
>     TypeConstructor QualIdent [Type]
>   | TypeVariable Int
>   | TypeGuard Int
>   | TypeArrow Type Type
>   | TypeSkolem Int
>   deriving (Eq,Ord,Show)

\end{verbatim}
The function \texttt{isArrowType} checks whether a type $\tau = \tau_1
\rightarrow \dots \rightarrow \tau_n \rightarrow \tau_{n+1}$
($n\geq0$) is a function type, i.e., whether $n > 0$ . The function
\texttt{arrowArity} returns the arity $n$ of a function type, the
function \texttt{arrowArgs} returns the list of types
\texttt{[$\tau_1$,$\dots$,$\tau_{n}$]}, \texttt{arrowBase} returns the
type $\tau_{n+1}$, and \texttt{arrowUnapply} combines
\texttt{arrowArgs} and \texttt{arrowBase} in one call.
\begin{verbatim}

> isArrowType :: Type -> Bool
> isArrowType (TypeArrow _ _) = True
> isArrowType _ = False

> arrowArity :: Type -> Int
> arrowArity = length . arrowArgs

> arrowArgs :: Type -> [Type]
> arrowArgs = fst . arrowUnapply

> arrowBase :: Type -> Type
> arrowBase = snd . arrowUnapply

> arrowUnapply :: Type -> ([Type],Type)
> arrowUnapply (TypeArrow ty1 ty2) = (ty1 : tys,ty)
>   where (tys,ty) = arrowUnapply ty2
> arrowUnapply ty = ([],ty)

\end{verbatim}
The methods \texttt{typeVars} and \texttt{typeSkolems} return a list
of all type variables and skolem types occurring in a type $\tau$,
respectively. Note that \texttt{TypeGuard} variables are not included
in the set of type variables because they cannot be generalized.
\begin{verbatim}

> class IsType t where
>   typeVars :: t -> [Int]
>   typeSkolems :: t -> [Int]

> instance IsType Type where
>   typeVars ty = vars ty []
>     where vars (TypeConstructor _ tys) tvs = foldr vars tvs tys
>           vars (TypeVariable tv) tvs = tv : tvs
>           vars (TypeGuard _) tvs = tvs
>           vars (TypeArrow ty1 ty2) tvs = vars ty1 (vars ty2 tvs)
>           vars (TypeSkolem _) tvs = tvs
>   typeSkolems ty = skolems ty []
>     where skolems (TypeConstructor _ tys) sks = foldr skolems sks tys
>           skolems (TypeVariable _) sks = sks
>           skolems (TypeGuard _) sks = sks
>           skolems (TypeArrow ty1 ty2) sks = skolems ty1 (skolems ty2 sks)
>           skolems (TypeSkolem k) sks = k : sks

\end{verbatim}
Qualified types represent types with class membership constraints. A
qualified type $\emph{cx}\Rightarrow\tau$ consists of a plain type
$\tau$ and a context \emph{cx}, which is a list of type predicates
$C_i\,\tau_i$ that must be satisfied. A type predicate $C_i\,\tau_i$
is satisfied if the type $\tau_i$ is an instance of class $C_i$. In
general, the types $\tau_i$ are simple type variables, which are free
in $\tau$. Type predicates where $\tau_i$ is not a simple type
variable may occur in intermediate contexts computed during type
inference. However, such predicates can be proved to be either
satisfied or not, or they can be transformed into simpler predicates
where all types are just type variables.

The order of predicates in a qualified type does not matter. In order
to define a canonical representation for qualified types, the compiler
sorts the predicates in the contexts of function types. The
non-standard \texttt{Ord} instance for type predicates sorts them
according to their type (variable) first so that constraints that
apply to the same type variable are grouped together.

\ToDo{Consider using true sets for the contexts of qualified types.}
\begin{verbatim}

> data QualType = QualType Context Type deriving (Eq,Show)
> type Context = [TypePred]
> data TypePred = TypePred QualIdent Type deriving (Eq,Show)

> instance Ord TypePred where
>   TypePred cls1 ty1 `compare` TypePred cls2 ty2 =
>     case ty1 `compare` ty2 of
>       LT -> LT
>       EQ -> cls1 `compare` cls2
>       GT -> GT

> qualType :: Type -> QualType
> qualType ty = QualType [] ty

> canonType :: QualType -> QualType
> canonType (QualType cx ty) = QualType (sort cx) ty

\end{verbatim}
The free and skolem variables of a qualified type are computed from
the plain type because the context of a qualified type must constrain
only variables that are free in the type itself.
\begin{verbatim}

> instance IsType QualType where
>   typeVars (QualType _ ty) = typeVars ty
>   typeSkolems (QualType _ ty) = typeSkolems ty

\end{verbatim}
Type schemes $\forall\overline{\alpha} . \emph{cx} \Rightarrow \tau$
introduce (universal) quantification of type variables in qualified
types. The universally quantified type variables in a type are
assigned increasing indices starting at 0. Therefore, it is sufficient
to record only the number of quantified type variables in the
\texttt{ForAll} constructor. The context \emph{cx} in a type scheme
must contain only predicates of the form $C_i\,\alpha_i$ where each
$\alpha_i$ is one of the universally quantified type variables.

In general, type variables are assigned indices from left to right in
the order of their occurrence in a type. However, a slightly different
scheme is used for types of data and newtype constructors. Here, the
type variables occurring on the left hand side of a declaration are
assigned indices $0, \dots, n-1$, where $n$ is the arity of the type
constructor, regardless of the order of their occurrence in the type.
Existentially quantified type variables that occur on the right hand
side of a type declaration are assigned ascending indices starting at
$n$ in the order of their occurrence. E.g., the type scheme $\forall 4
. (2 \rightarrow 1) \rightarrow (0 \rightarrow 3) \rightarrow
\texttt{T}\,0\,1$ is used for constructor \texttt{C} in the
declaration
\begin{verbatim}
  data T a b = forall c d . C (d -> b) (a -> c)
\end{verbatim}
Thus, it is very easy to distinguish universally and existentially
quantified type variables in the types of data and newtype
constructors. Given type scheme $\forall m . \tau_1 \rightarrow \dots
\tau_l \rightarrow T\,0\dots (n-1)$ for a constructor of type $T$, we
know that the type variables with indices $0, \dots, n-1$ are
universally quantified and the type variables with indices $n, \dots,
m-1$ are existentially quantified.
\begin{verbatim}

> data TypeScheme = ForAll Int QualType deriving (Eq,Show)

> instance IsType TypeScheme where
>   typeVars (ForAll _ ty) = [tv | tv <- typeVars ty, tv < 0]
>   typeSkolems (ForAll _ ty) = typeSkolems ty

\end{verbatim}
The functions \texttt{monoType} and \texttt{polyType} translate a type
$\tau$ into a monomorphic type scheme $\forall.\tau$ and a polymorphic
type scheme $\forall\overline{\alpha}.\tau$, respectively, where
$\overline{\alpha} = \emph{vars}(\tau)$. The function
\texttt{typeScheme} translates a qualified type $\emph{cx} \Rightarrow
\tau$ into a polymorphic type scheme $\forall\overline{\alpha}.
\emph{cx} \Rightarrow \tau$. Note that neither \texttt{polyType} nor
\texttt{typeScheme} renumber the type variables in their argument
types.
\begin{verbatim}

> monoType :: Type -> TypeScheme
> monoType ty = ForAll 0 (qualType ty)

> polyType :: Type -> TypeScheme
> polyType ty = typeScheme (qualType ty)

> typeScheme :: QualType -> TypeScheme
> typeScheme ty = ForAll (maximum (-1 : typeVars ty) + 1) ty

\end{verbatim}
The function \texttt{rawType} strips the quantifier and context from a
type scheme.
\begin{verbatim}

> rawType :: TypeScheme -> Type
> rawType (ForAll _ (QualType _ ty)) = ty

\end{verbatim}
There are a few predefined types. Note that the identifiers of the
primitive types \texttt{()}, \texttt{[a]}, and the tuple types must
never be qualified with a module prefix.
\begin{verbatim}

> isPrimTypeId :: QualIdent -> Bool
> isPrimTypeId tc = tc `elem` [qUnitId,qListId] || isQTupleId tc

> unitType,boolType,charType,intType,floatType,stringType,successType :: Type
> unitType = TypeConstructor qUnitId []
> boolType = TypeConstructor qBoolId []
> charType = TypeConstructor qCharId []
> intType = TypeConstructor qIntId []
> floatType = TypeConstructor qFloatId []
> stringType = listType charType
> successType = TypeConstructor qSuccessId []

> listType,ioType :: Type -> Type
> listType ty = TypeConstructor qListId [ty]
> ioType ty = TypeConstructor qIOId [ty]

> tupleType :: [Type] -> Type
> tupleType tys = TypeConstructor (qTupleId (length tys)) tys

> typeVar :: Int -> Type
> typeVar = TypeVariable

\end{verbatim}
The variable \texttt{guardTypes} maintains the list of types
admissible for guard expressions. The first type of this list
(\texttt{Success}), is used as default type if the guard's type cannot
be determined otherwise.
\begin{verbatim}

> guardTypes :: [Type]
> guardTypes = [successType,boolType]

\end{verbatim}