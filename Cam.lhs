% -*- LaTeX -*-
% $Id: Cam.lhs 3000 2010-08-30 19:33:17Z wlux $
%
% Copyright (c) 1998-2009, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Cam.lhs}
\section{Abstract Machine Code}
This section describes the instruction set of the abstract machine.
\begin{verbatim}

> module Cam where
> import Char

\end{verbatim}
An abstract machine code module consists of a list of import, data,
and function declarations. A data declaration defines the constructors
of a data type together with their argument types. A function
declaration comprises the function's name, arguments, and code.
\begin{verbatim}

> type Module = [Decl]
> data Decl =
>     ImportDecl Name
>   | DataDecl Name [Name] [ConstrDecl]
>   | FunctionDecl Name [Name] Stmt
>   deriving (Eq,Show)
> data ConstrDecl = ConstrDecl Name [Type] deriving (Eq,Show)
> data Type =
>     TypeVar Name
>   | TypeApp Name [Type]
>   | TypeArr Type Type
>   deriving (Eq,Show)

> splitCam :: Module
>          -> ([Name],[(Name,[Name],[ConstrDecl])],[(Name,[Name],Stmt)])
> splitCam = foldr split ([],[],[])
>   where split (ImportDecl m) ~(ms,ds,fs) = (m:ms,ds,fs)
>         split (DataDecl t vs cs) ~(ms,ds,fs) = (ms,(t,vs,cs):ds,fs)
>         split (FunctionDecl f vs st) ~(ms,dss,fs) = (ms,dss,(f,vs,st):fs)

\end{verbatim}
\subsection{Instruction Set}
The instruction set of the abstract machine is a simple block
structured language, which is related to that of the STG and JUMP
machines~\cite{Peyton92:STG, ChakravartyLock97:Jump}. However, in
contrast to these abstract machines and similar to GRIN
code~\cite{BoquistJohnsson96:GRIN, Boquist99:Thesis}, evaluation of
nodes is made explicit in the Curry abstract machine.

\texttt{Return} $e$ allocates a fresh node for the expression $e$ and
returns its address.

\texttt{Eval} $x$ evaluates the node bound to $x$ to head normal form
and returns its address. If the node is already in head normal form,
\texttt{eval}~$x$ is equivalent to \texttt{return}~$x$.

\texttt{Exec} $f(x_1,\dots,x_n)$, where $n$ is the arity of $f$,
enters the global function $f$ and passes the nodes referenced by
$x_1,\dots,x_n$ as arguments to it.

\texttt{Ccall} $h$ $(\emph{ty})$\emph{cc} evaluates the C code
\emph{cc}, allocates a fresh node for its result, and returns the
address of that node. \emph{Cc} is either a static function call
$f((\emph{ty}_1)x_1,\dots,(\emph{ty}_k)x_k)$, a dynamic function call
$(*x)((\emph{ty}_1)x_1,\dots,(\emph{ty}_k)x_k)$, or the address of a
variable \texttt{\&}$x$. The type \emph{ty} specifies the type of
\emph{cc}'s result and $\emph{ty}_1,\dots,\emph{ty}_k$ specify the
types of the arguments $x_1,\dots,x_k$. \emph{Ty} should be either
\texttt{TypePtr} or \texttt{TypeFunPtr} when computing the address of
a variable. If \emph{ty} is omitted, the C function is assumed to
return no result and the constant \texttt{()} is returned instead. The
optional file name $h$ specifies the name of a C header file, which
contains a prototype of $f$ or a declaration of $x$, respectively.

A statement sequence $x$ \texttt{<-} \emph{st$_1$}\texttt{;}
\emph{st$_2$} first executes \emph{st$_1$} and binds the (fresh)
variable $x$ to the computed result. It then executes \emph{st$_2$} in
the extended environment.

\texttt{Let} \texttt{\lb}~$x_1$\texttt{=}$e_1$\texttt{;}
\dots\texttt{;} $x_n$\texttt{=}$e_n$~\texttt{\rb} \texttt{in}
\emph{st} allocates new nodes for the expressions $e_1,\dots,e_n$,
binds the variables $x_1,\dots,x_n$ to the respective nodes, and then
executes \emph{st} in the extended environment. The bindings in a
\texttt{let} statement may be mutually recursive. Note that the
possibility to introduce mutually recursive bindings is the only
raison d'\^etre for \texttt{let} statements. Non-recursive
\texttt{let} bindings can be removed using \texttt{let}
\texttt{\lb}~$x$ \texttt{=} $e$~\texttt{\rb} \texttt{in} \emph{st}
$\null\equiv\null$ $x$ \texttt{<-} \texttt{return} $e$\texttt{;}
\emph{st}.

\texttt{Switch} \emph{rf} $x$
\texttt{\lb}~$t_1$\texttt{:}\emph{st$_1$} \texttt{|} $\dots$
\texttt{|} $t_n$\texttt{:}\emph{st$_n$}~\texttt{\rb} selects the
(first) alternative $t_i$\texttt{:}\emph{st$_i$} whose pattern $t_i$
matches the node bound to $x$ and executes the statement
\emph{st$_i$}. When $x$ is bound to a free variable node and
$\emph{rf}=\texttt{flex}$, an alternative is selected
non-deterministically and the variable is instantiated to a fresh
instance of its pattern. If $x$ is bound to a free variable node and
$\emph{rf}=\texttt{rigid}$, the current thread is suspended until the
variable is instantiated and then the matching alternative is
selected.

\texttt{Choice} \texttt{\lb}~\emph{st$_1$} \texttt{|} $\dots$
\texttt{|} \emph{st$_n$}~\texttt{\rb} non-deterministically executes a
statement from $\emph{st$_1$},\dots,\emph{st$_n$}$.
\begin{verbatim}

> data Stmt =
>     Return Expr
>   | Eval Name
>   | Exec Name [Name]
>   | CCall (Maybe String) CRetType CCall
>   | Seq Stmt0 Stmt
>   | Let [Bind] Stmt
>   | Switch RF Name [Case]
>   | Choice [Alt]
>   deriving (Eq,Show)
> data Stmt0 = Name :<- Stmt deriving (Eq,Show)

> type Alt = Stmt
> data Bind = Bind Name Expr deriving (Eq,Show)
> data RF = Rigid | Flex deriving (Eq,Show)
> data CCall =
>     StaticCall String [(CArgType,Name)]
>   | DynamicCall Name [(CArgType,Name)]
>   | StaticAddr String
>   deriving (Eq,Show)

\end{verbatim}
The abstract machine supports literal constants, data constructors,
partial applications (of data constructors and functions), function
closures, and logical variables as nodes. Similar to the STG
machine~\cite{Peyton92:STG}, we distinguish non-updatable
\texttt{Closure} and updatable \texttt{Lazy} application nodes. An
expression \texttt{Var}~$x$ does not denote a fresh node, but a
reference to the node bound to $x$.
\begin{verbatim}

> data Literal =
>     Char Char
>   | Int Integer
>   | Integer Integer
>   | Float Double deriving (Eq,Show)

> data Expr =
>     Lit Literal
>   | Constr Name [Name]
>   | Papp Name [Name]
>   | Closure Name [Name]
>   | Lazy Name [Name]
>   | Free
>   | Var Name
>   deriving (Eq,Show)

\end{verbatim}
Each case of a switch statement associates a pattern with a statement.
The patterns are either literal constants or a data constructor
patterns. In the latter case, the names in a pattern are bound to the
corresponding arguments of the data constructor before executing its
associated statement. A default pattern allows matching all remaining
cases in a switch statement.
\begin{verbatim}

> data Case = Case Tag Stmt deriving (Eq,Show)
> data Tag = LitCase Literal | ConstrCase Name [Name] | DefaultCase
>            deriving (Eq,Show)

\end{verbatim}
Argument and result types of C functions are restricted to booleans,
characters, integer numbers, floating-point numbers, and (untyped)
pointers and function pointers at present. Two special cases are
present in order to handle passing stable and node pointers to and
from foreign functions. Passing node pointers is an experimental
feature that should be used with care. The result type of a C function
may be omitted when the function is called only for its side effect.
In this case, the abstract machine will use the unit constructor
\texttt{()} as result of the call.
\begin{verbatim}

> type CRetType = Maybe CArgType
> data CArgType =
>     TypeBool | TypeChar | TypeInt | TypeFloat
>   | TypePtr | TypeFunPtr | TypeStablePtr | TypeNodePtr
>   deriving (Eq,Show)

\end{verbatim}
\subsection{External Names}
External names in the abstract machine code must be composed of
characters and underscores. Therefore the names of Curry operators
have to be encoded. We use the following strategy for mangling Curry
identifiers. All alpha-numeric characters in an identifier are left
unchanged, all other characters are replaced by sequences composed of
an underscore character, the (decimal) character code, and another
underscore character. As a minor exception from this rule, the dot
separating the module name from the unqualified name in a qualified
identifier is replaced by two consecutive underscores.
\begin{verbatim}

> newtype Name = Name String deriving (Eq,Ord)
> instance Show Name where
>   showsPrec _ (Name name) = showString name

\end{verbatim}
The mangling strategy is implemented by the functions \texttt{mangle}
and \texttt{mangleQualified} below. The inverse operation is
implemented by the function \texttt{demangle}.
\begin{verbatim}

> mangle :: String -> Name
> mangle cs = Name (mangleIdent cs)
>   where mangleIdent [] = []
>         mangleIdent (c:cs)
>           | isAlphaNum c = c : mangleIdent cs
>           | otherwise = '_' : show (ord c) ++ '_' : mangleIdent cs

> mangleQualified :: String -> Name
> mangleQualified cs
>   | null mname = Name name'
>   | otherwise = Name (mname' ++ "__" ++ name')
>   where (mname,name) = splitQualified cs
>         Name mname' = mangle mname
>         Name name'  = mangle name

> demangle :: Name -> String
> demangle (Name cs) = demangleName cs
>   where demangleName [] = []
>         demangleName (c:cs)
>           | c == '_' = unescape ds cs'
>           | otherwise = c : demangleName cs
>           where (ds,cs') = span isDigit cs
>         unescape ds ('_':cs)
>           | null ds = '.' : demangleName cs
>           | n <= ord maxBound = chr n : demangleName cs
>           | otherwise = '_' : ds ++ '_' : demangleName cs
>           where n = read ds
>         unescape ds cs = '_':ds ++ demangleName cs

\end{verbatim}
In order to split a qualified name into its module prefix and the
unqualified name, the function \texttt{splitQualified} assumes that
valid module identifiers have to start with an alphabetic character
and that the unqualified name must not be empty.

\ToDo{The heuristics implemented by \texttt{splitQualified} fails for
lifted local functions, as the compiler prefixes their names with the
names of the enclosing functions and uses a dot as separator.}
\begin{verbatim}

> splitQualified :: String -> (String,String)
> splitQualified [] = ([],[])
> splitQualified (c:cs)
>   | isAlpha c =
>       case break ('.' ==) cs of
>         (_,[]) -> ([],c:cs)
>         (prefix,'.':cs')
>           | null cs' || isDigit (head cs') -> ([],c:cs)
>           | otherwise -> (c:prefix `sep` prefix',name)
>           where (prefix',name) = splitQualified cs'
>                 sep cs1 cs2
>                   | null cs2 = cs1
>                   | otherwise = cs1 ++ '.':cs2
>   | otherwise = ([],c:cs)

\end{verbatim}
\input{CamPP.lhs} % \subsection{Pretty-printing Abstract Machine Code}
\input{CamParser.lhs} % \subsection{Parsing Abstract Machine Code}
