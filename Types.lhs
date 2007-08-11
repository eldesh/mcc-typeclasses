% -*- LaTeX -*-
% $Id: Types.lhs 2434 2007-08-11 12:39:47Z wlux $
%
% Copyright (c) 2002-2007, Wolfgang Lux
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
A type is either a type constructor, a type variable, or an
application of a type to another type. The \texttt{TypeConstrained}
and \texttt{TypeSkolem} constructors represent two special cases of
type variables. A \texttt{TypeConstrained} variable represents a type
variable that is restricted to a particular set of types. At present,
this is used for typing guard expressions, which are restricted to be
either of type \texttt{Bool} or of type \texttt{Success}, and integer
literals in patterns, which are restricted to types \texttt{Int} and
\texttt{Float}. If the type is not restricted, it defaults to the
first type from the constraint list. A \texttt{TypeSkolem} variable is
used for handling skolem types, which result from matching data
constructors with existentially quantified types. Since arrow types
are used so frequently, we use \texttt{TypeArrow} $t_1$ $t_2$
consistently as a shorthand for the application of the arrow type
constructor \texttt{(->)} to the two types $t_1$ and $t_2$.

Type variables are represented with deBruijn style indices. Universally
quantified type variables are assigned indices in the order of their
occurrence in the type from left to right. This leads to a canonical
representation of types where $\alpha$-equivalence of two types
coincides with equality of the representation.

Note that even though \texttt{TypeConstrained} variables use indices
as well, these variables must never be quantified.

\ToDo{Use \texttt{TypeApply .\ TypeApply qArrowId} instead of
  \texttt{TypeArrow}?}
\begin{verbatim}

> data Type =
>     TypeConstructor QualIdent
>   | TypeVariable Int
>   | TypeConstrained [Type] Int
>   | TypeSkolem Int
>   | TypeApply Type Type
>   | TypeArrow Type Type
>   deriving (Eq,Ord,Show)

\end{verbatim}
The function \texttt{applyType} applies a type to a list of argument
types. Note that it carefully converts an application of the arrow
type constructor to two argument types into an arrow type. The
function \texttt{unapplyType} decomposes a type into a root type and a
list of argument types such that the root type is either a type
constructor, a type variable, or a skolem type. If the \texttt{dflt}
argument of \texttt{unapplyType} is \texttt{True}, constrained type
variables are fixed to their first alternative, otherwise they are
handled like type variables. The function \texttt{rootOfType} returns
the name of the type constructor at the root of a type. This function
must not be applied to a type whose root is a type variable or a
skolem type.
\begin{verbatim}

> applyType :: Type -> [Type] -> Type
> applyType (TypeConstructor tc) tys
>   | tc == qArrowId && length tys == 2 = TypeArrow (tys!!0) (tys!!1)
> applyType (TypeApply (TypeConstructor tc) ty) tys
>   | tc == qArrowId && length tys == 1 = TypeArrow ty (head tys)
> applyType ty tys = foldl TypeApply ty tys

> unapplyType :: Bool -> Type -> (Type,[Type])
> unapplyType dflt ty = unapply ty []
>   where unapply (TypeConstructor tc) tys = (TypeConstructor tc,tys)
>         unapply (TypeVariable tv) tys = (TypeVariable tv,tys)
>         unapply (TypeConstrained tys tv) tys'
>           | dflt = unapply (head tys) tys'
>           | otherwise = (TypeConstrained tys tv,tys')
>         unapply (TypeSkolem k) tys = (TypeSkolem k,tys)
>         unapply (TypeApply ty1 ty2) tys = unapply ty1 (ty2:tys)
>         unapply (TypeArrow ty1 ty2) tys =
>           (TypeConstructor qArrowId,ty1:ty2:tys)

> rootOfType :: Type -> QualIdent
> rootOfType ty =
>   case fst (unapplyType True ty) of
>     TypeConstructor tc -> tc
>     _ -> error "internal error: rootOfType"

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
respectively. Note that \texttt{TypeConstrained} variables are not
included in the set of type variables because they cannot be
generalized.
\begin{verbatim}

> class IsType t where
>   typeVars :: t -> [Int]
>   typeSkolems :: t -> [Int]

> instance IsType a => IsType [a] where
>   typeVars = concatMap typeVars
>   typeSkolems = concatMap typeSkolems

> instance IsType Type where
>   typeVars ty = vars ty []
>     where vars (TypeConstructor _) tvs = tvs
>           vars (TypeVariable tv) tvs = tv : tvs
>           vars (TypeConstrained _ _) tvs = tvs
>           vars (TypeSkolem _) tvs = tvs
>           vars (TypeApply ty1 ty2) tvs = vars ty1 (vars ty2 tvs)
>           vars (TypeArrow ty1 ty2) tvs = vars ty1 (vars ty2 tvs)
>   typeSkolems ty = skolems ty []
>     where skolems (TypeConstructor _) sks = sks
>           skolems (TypeVariable _) sks = sks
>           skolems (TypeConstrained _ _) sks = sks
>           skolems (TypeSkolem k) sks = k : sks
>           skolems (TypeApply ty1 ty2) sks = skolems ty1 (skolems ty2 sks)
>           skolems (TypeArrow ty1 ty2) sks = skolems ty1 (skolems ty2 sks)

\end{verbatim}
Qualified types represent types with class membership constraints. A
qualified type $\emph{cx}\Rightarrow\tau$ consists of a plain type
$\tau$ and a context \emph{cx}, which is a list of type predicates
$C_i\,\tau_i$ that must be satisfied. A type predicate $C_i\,\tau_i$
is satisfied if the type $\tau_i$ is an instance of class $C_i$.
Normally, each type $\tau_i$ has the form $\alpha\,\tau_1,\dots\tau_k$
($k\geq0$), where $\alpha$ is a type variable and $\tau_1,\dots\tau_k$
are types. Type predicates where $\tau_i$ has a different form may
occur in intermediate contexts computed during type inference.
However, such predicates can be proved to be either satisfied or not,
or they can be transformed into simpler predicates where all types are
of the form $\alpha\,\tau_1,\dots\tau_k$.

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

> unqualType :: QualType -> Type
> unqualType (QualType _ ty) = ty

> canonType :: QualType -> QualType
> canonType = contextMap sort

> contextMap :: (Context -> Context) -> QualType -> QualType
> contextMap f (QualType cx ty) = QualType (f cx) ty

\end{verbatim}
Usually, the free and skolem variables of the context of a qualified
type are free in the plain type itself, but this is not necessarily
the case.
\begin{verbatim}

> instance IsType QualType where
>   typeVars (QualType cx ty) = typeVars ty ++ typeVars cx
>   typeSkolems (QualType cx ty) = typeSkolems ty ++ typeSkolems cx

> instance IsType TypePred where
>   typeVars (TypePred _ ty) = typeVars ty
>   typeSkolems (TypePred _ ty) = typeSkolems ty

\end{verbatim}
Type schemes $\forall\overline{\alpha} . \emph{cx} \Rightarrow \tau$
introduce (universal) quantification of type variables in qualified
types. The universally quantified type variables in a type are
assigned increasing indices starting at 0. Therefore, it is sufficient
to record only the number of quantified type variables in the
\texttt{ForAll} constructor. The context \emph{cx} of a type scheme
must contain only predicates of the form
$C\,(\alpha\,\tau_1\dots\tau_k)$ ($k\geq0$) where the type variable
$\alpha$ and the free variables of the types $\tau_1,\dots,\tau_k$ are
either free in the plain type $\tau$ or are monomorphic type variables
that are bound in the type environment.

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

> tmap :: (QualType -> QualType) -> TypeScheme -> TypeScheme
> tmap f (ForAll n ty) = ForAll n (f ty)

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
primitive types \texttt{()}, \texttt{[a]}, \texttt{a -> b}, and the
tuple types must never be qualified with a module prefix.
\begin{verbatim}

> isPrimTypeId :: QualIdent -> Bool
> isPrimTypeId tc = tc `elem` [qUnitId,qListId,qArrowId] || isQTupleId tc

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
The variables \texttt{numTypes} and \texttt{fracTypes} maintain the
lists of types admissible for ambiguous types with \texttt{Num} and
\texttt{Fractional} constraints, respectively.
\begin{verbatim}

> numTypes, fracTypes :: [Type]
> numTypes = [intType,floatType]
> fracTypes = tail numTypes

\end{verbatim}
