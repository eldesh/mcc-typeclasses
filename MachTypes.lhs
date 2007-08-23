% -*- LaTeX -*-
% $Id: MachTypes.lhs 2452 2007-08-23 22:51:27Z wlux $
%
% Copyright (c) 1998-2007, Wolfgang Lux
% See LICENSE for the full license.
%
\subsection{Basic Types}
\begin{verbatim}

> module MachTypes where
> import Env
> import Error
> import Combined
> import IO(IOMode(..),Handle)
> import IOExts()

\end{verbatim}
\emph{The empty import of module \texttt{IOExts} is necessary in order
to import the instance declarations for the \texttt{Ref} when
compiling with hbc.}

In our abstract machine interpreter, we do not interpret the abstract
machine statements directly, but instead convert each statement into a
state transformer when the program is loaded. Using continuation
passing style, every statement is parameterized by the next
statement(s) to be executed. The whole program then finally delivers
some result. We use a combined
monad~\cite{LiangHudakJones95:ModInterp} which encapsulates the
current machine state and also encapsulates the error handling.
Finally, the combined monad is parameterized by an IO monad because we
make use of mutable references in the implementation of the machine.
Not very surprisingly, the final result of a computation is the final
state.
\begin{verbatim}

> type MachStateT a = StateT State (ErrorT IO) a
> type Instruction = MachStateT (Maybe State)

\end{verbatim}
\ToDo{Should we define \texttt{Instruction} using a \texttt{newtype}
declaration? This could make a lot of \texttt{Show} instances
derivable.}

In order to implement the heap we use mutable references, which are
provided by most Haskell implementations. Every node allocated in the
heap is also assigned an ``address''. We use a simple counter for that
purpose.
\subsubsection{Functions}
A function is described by its name, entry point, and arity.
\begin{verbatim}

> type Function = (String,Instruction,Int)

\end{verbatim}
\subsubsection{Graph Nodes}
The heap contains nodes which are used to build a graph corresponding
to the final result of the goal being evaluated.

Integer and floating-point numbers are represented by the
corresponding cases in the \texttt{Node} type and consists of the
number's value.

A variable node represents an unbound variable. It has three fields,
the first contains a list of constraints for the variable, the second
contains the list of threads that have been delayed for that variable,
and the third contains the search space in which the variable was
created. Once the variable is instantiated the node will be
overwritten destructively.

Indirection nodes are used when a variable or a lazy application node
is overwritten in order to preserve the sharing of nodes. An
indirection node solely consists of a pointer to the new node.

Partial applications nodes represent partial applications of data
constructors and functions.

Closure and lazy application nodes represent functions and their
applications. A plain function corresponds to a closure node without
arguments. A closure node consists of the code to be executed for the
function, the arity, and the list of arguments to which the function
has been applied. In addition, the name of the function is included in
order to make the output more readable. Besides that it has no
semantic meaning.

In contrast to closure nodes, lazy application nodes are overwritten
with their result after they have been evaluated. In addition to the
fields of a closure node, lazy application nodes also include the
search space in which the node was constructed.

In order to prevent multiple threads from evaluating the same
application, lazy application nodes are overwritten by a queue-me node
when a thread starts their evaluation. A wait queue similar to
variable nodes is used to collect the threads that have been delayed
on this node. Once evaluation of a lazy application completes
successfully, the queue-me node is overwritten by the result of the
evaluation.

Search continuation nodes are used to represent the alternative
continuations returned by the \texttt{try} operator. A search
continuation saves the goal application and variable of the goal being
evaluated. In addition, the state of all local threads and the
corresponding search space are saved in this node.
\begin{verbatim}

> data NodeTag =
>     CharTag Char | IntTag Integer | FloatTag Double
>   | ConstructorTag Int String Int | VariableTag
>   | ClosureTag | LazyTag | QueueMeTag
>   | IndirTag | SearchTag
>   deriving Show
> instance Eq NodeTag where
>   CharTag c == CharTag d = c == d
>   IntTag i == IntTag j = i == j
>   FloatTag e == FloatTag f = e == f
>   ConstructorTag t1 _ _ == ConstructorTag t2 _ _ = t1 == t2
>   VariableTag == VariableTag = True
>   ClosureTag == ClosureTag = True
>   LazyTag == LazyTag = True
>   QueueMeTag == QueueMeTag = True
>   IndirTag == IndirTag = True
>   SearchTag == SearchTag = True
>   _ == _ = False

> data Node =
>     CharNode Char | IntNode Integer | FloatNode Double
>   | ConstructorNode Int String [NodePtr]
>   | VarNode [Constraint] ThreadQueue SearchSpace
>   | ClosureNode String Int Instruction [NodePtr]
>   | LazyNode String Int Instruction [NodePtr] SearchSpace
>   | QueueMeNode ThreadQueue SearchSpace
>   | IndirNode NodePtr
>   | SearchContinuation NodePtr NodePtr ThreadQueue SearchSpace

> instance Show Node where
>   showsPrec p (CharNode c) =
>     showParen (p >= 10) $ showString "CharNode " . shows c
>   showsPrec p (IntNode i) =
>     showParen (p >= 10) $ showString "IntNode " . shows i
>   showsPrec p (FloatNode f) =
>     showParen (p >= 10) $ showString "FloatNode " . shows f
>   showsPrec p (ConstructorNode tag name args) = showParen (p >= 10) $
>     showString "ConstructorNode " . shows tag . showChar ' ' .
>       showString name . flip (foldr showArg) args
>     where showArg arg = showChar ' ' . showsPrec 1 arg
>   showsPrec p (VarNode constraints waitqueue space) = showParen (p >= 10) $
>     showString "VarNode " . showsPrec 1 constraints . showChar ' ' .
>       showsPrec 1 waitqueue . showChar ' ' . showsPrec 1 space
>   showsPrec p (ClosureNode name arity code args) = showParen (p >= 10) $
>     showString "ClosureNode " . showString name . showChar ' ' .
>       shows arity . flip (foldr showArg) args
>     where showArg arg = showChar ' ' . showsPrec 1 arg
>   showsPrec p (LazyNode name arity code args space) = showParen (p >= 10) $
>     showString "LazyNode " . showString name . showChar ' ' .
>       shows arity . flip (foldr showArg) args . showChar ' ' .
>         showsPrec 1 space
>     where showArg arg = showChar ' ' . showsPrec 1 arg
>   showsPrec p (QueueMeNode waitqueue space) = showParen (p >= 10) $
>     showString "QueueMeNode " . showsPrec 1 waitqueue . showChar ' ' .
>       showsPrec 1 space
>   showsPrec p (IndirNode ptr) =
>     showParen (p >= 10) $ showString "IndirNode " . showsPrec 1 ptr
>   showsPrec p (SearchContinuation app var rq space) = showParen (p >= 10) $
>     showString "SearchContinuation " . showsPrec 1 app . showChar ' ' .
>       showsPrec 1 var . showChar ' ' . showsPrec 1 rq . showChar ' ' .
>         showsPrec 1 space

> data NodePtr = Ptr Integer (Ref Node)
> instance Eq NodePtr where
>   Ptr adr1 _ == Ptr adr2 _ = adr1 == adr2
> instance Ord NodePtr where
>   Ptr adr1 _ `compare` Ptr adr2 _ = adr1 `compare` adr2
> instance Show NodePtr where
>   showsPrec _ (Ptr adr _) = showString "node@" . shows adr

> nodeTag :: Node -> NodeTag
> nodeTag (CharNode c) = CharTag c
> nodeTag (IntNode i) = IntTag i
> nodeTag (FloatNode f) = FloatTag f
> nodeTag (ConstructorNode t c xs) = ConstructorTag t c (length xs)
> nodeTag (VarNode _ _ _) = VariableTag
> nodeTag (ClosureNode _ _ _ _) = ClosureTag
> nodeTag (LazyNode _ _ _ _ _) = LazyTag
> nodeTag (QueueMeNode _ _) = QueueMeTag
> nodeTag (IndirNode _) = IndirTag
> nodeTag (SearchContinuation _ _ _ _) = SearchTag

> nilTag, consTag, unitTag, successTag :: NodeTag
> nilTag  = ConstructorTag 0 "[]" 0
> consTag = ConstructorTag 1 ":" 2
> unitTag = ConstructorTag 0 "()" 0
> successTag = ConstructorTag 0 "Success" 0

> isTupleName :: String -> Bool
> isTupleName ('(':',':cs) = dropWhile (',' ==) cs == ")"
> isTupleName _ = False

\end{verbatim}
\subsubsection{Machine State}
The abstract machine uses a data stack for the arguments of a
function, a return stack to save the return context of a function
call, a choicepoint stack to implement global search via backtracking,
and a search context stack for (nested) encapsulated search
invocations. The state of the abstract machine is composed of the
following information:
\begin{verbatim}

> data State = State {
>     tid :: Integer,           -- thread id of running thread
>     env :: LocalEnv,          -- local environment
>     ds :: DataStack,          -- argument stack
>     rs :: ContStack,          -- return stack
>     rq :: ThreadQueue,        -- list of runnable threads
>     hp :: Integer,            -- ``allocation pointer'' in the heap
>     bp :: FailureStack,       -- choicepoint stack
>     tp :: Trail,              -- trail
>     ct :: Integer,            -- thread counter
>     sc :: SearchContext,      -- current search context
>     ss :: SearchSpace         -- pointer to current search space
>   } deriving Show

\end{verbatim}
The local environment maps the names of the local variables onto the
addresses of the associated nodes.
\begin{verbatim}

> type LocalEnv = Env String NodePtr

\end{verbatim}
The data stack is implemented as a list of nodes addresses.
\begin{verbatim}

> type DataStack = [NodePtr]

\end{verbatim}
The return stack has to maintain the return address of a function and
also saves the caller's local environment.
\begin{verbatim}

> type ContStack = [Cont]
> data Cont = Cont Instruction LocalEnv

> instance Show Cont where
>   showsPrec p (Cont ip env) = showParen (p >= 10) $
>     showString "Cont <<Instruction>> " . showsPrec 10 env

\end{verbatim}
In a choice point, all machine registers have to be saved so that the
machine state can be restored upon backtracking. In addition, the next
instruction to be executed after backtracking must be saved here. Note
that choice points are used only in the global search space, so the
current search space does not have to be saved.
\begin{verbatim}

> type FailureStack = [Choicepoint]
> data Choicepoint = Choicepoint Instruction Integer LocalEnv DataStack
>                                ContStack ThreadQueue Trail

> instance Show Choicepoint where
>   showsPrec p (Choicepoint ip tid env ds rs rq tp) = showParen (p >= 10) $
>     showString "Choicepoint <<Instruction>> " . shows tid .
>       showsPrec 10 env . showChar ' ' . shows ds . showChar ' ' . shows rs .
>         showChar ' ' . shows rq . showChar ' ' . shows tp

\end{verbatim}
\subsubsection{Threads}
In order to implement the concurrent evaluation, a simple thread
facility is integrated into the abstract machine. Every computation is
executed within a thread. The abstract machine is executing the
running thread. A list of threads which are runnable but not active
are saved in the ready queue. Threads which are suspended due to an
access to an unbound variable or locked application node are collected
in the wait queues of the corresponding node.

A thread can be member of more than one queue which makes it possible
to wake a thread using one of a list of conditions. This is
implemented by including a \texttt{ThreadSurrogate} for the thread in
each of the queues. As soon as the thread is woken through one of the
queues, all of its surrogates are released.

A context switch will occur only if the current thread suspends itself
or exits. The current thread suspends itself if it finds an
uninstantiated variable in a demanded position during pattern matching
inside a rigid function or when it tries to evaluate a locked application
node. In addition, a thread may reschedule itself in order to allow
deterministic computations to be performed when the current thread can
otherwise proceed only non-deterministically.

The information about a thread which is not running is saved in a
thread node that is allocated in the heap. Every thread frame
includes a unique thread id, which just provides a nice means
to display threads during tracing and otherwise has no functionality.
For the running thread, this id is maintained in the \texttt{tid}
machine register.
\begin{verbatim}

> type ThreadQueue = [Thread]
> newtype ThreadPtr = ThreadPtr (Ref (Maybe Thread))
> data Thread = Thread Integer Instruction LocalEnv DataStack ContStack
>             | ThreadSurrogate Integer ThreadPtr

> instance Show Thread where
>   showsPrec p (Thread id ip env ds rs) = showParen (p >= 10) $
>     showString "Thread " . shows id . showString " <<Instruction>> " .
>       showsPrec 10 env . showChar ' ' . shows ds . showChar ' ' . shows rs
>   showsPrec p (ThreadSurrogate id _) = showParen (p >= 10) $
>     showString "ThreadSurrogate " . shows id

> instance Show ThreadPtr where
>   showsPrec p (ThreadPtr _) = showString "<<ThreadPtr>>"

\end{verbatim}
\subsubsection{Local Search Spaces}
Local search spaces are used as a foundation for the implementation of
encapsulated search. They serve as a means to isolate the effects
of the different alternatives of a non-deterministic
computation. Logic variables introduced during the unification of
argument expressions are available only to the computation space in
which they were created and to local spaces defined inside that
space. They can be bound only by computations operating in
the same local space. Computations in a local space may have non-local
effects, though. They can force the evaluation of an application node
to weak head normal form. Because of the strong separation of the
search spaces, these evaluations need not be undone when the local
computation fails.\footnote{The same is in fact true for the usual
implementation using backtracking and a depth first search, but it is
not easy to detect such computations, while for local spaces simply
the membership in a given search space has to be tested.}

A new local space is introduced by the primitive function
\texttt{try}, which reduces its argument function in this space until
the computation either fails, succeeds, or splits
non-deterministically into several alternative computations. In these
cases \texttt{try} returns either an empty list, a singleton list
containing one search continuation in solved form, or a list with
one search continuation for each possible continuation.

In order to maintain the different bindings of variables and lazy
applications, each call to \texttt{try} uses a new search space with
its own set of bindings. Thus, \texttt{try} can be used to implement
different search strategies besides the depth-first search strategy
usually employed by implementations of logic and functional logic
languages. In addition, it allows -- to a certain extent -- to
encapsulate the non-determinism of a computation by lifting it into a
list of alternatives.  See~\cite{HanusSteiner98:Control} and the
diploma thesis of Frank Steiner~\cite{Steiner97:Diplom} for a more
detailed account on the operational semantics of the encapsulated
search.

Whenever \texttt{try} is invoked, the current machine state including
the current search space has to be saved. A \texttt{SearchContext} is
allocated for that purpose on the control stack. This state does not
include the instruction pointer because the return address for the
\texttt{try} call is already saved in the corresponding environment
frame. In addition, the \texttt{SearchContext} saves the reference to
a (locked) lazy application, which will be updated when the evaluation
of the search goal finally succeeds, and the variable that was applied
to the goal in order to start its evaluation.

A search space maintains the bindings of all local variables and lazy
applications. As we use destructive updates on the graph, this means
that we have to save the old state of the variables, i.e., the one
outside the search space, when the variable is updated. This simply
means that the trail has to be saved. In addition, we must save the
state of the variables and lazy application nodes inside the search
space. This is handled by adding a second trail, called the script, to
the search space.\footnote{The name is borrowed from Amoz, the
abstract machine for Oz~\cite{MehlScheidhauerSchule95:Amoz}, which
uses a similar strategy.} We use the fact that the state of a search
space that was restored from a search continuation is shared by the
current search space and maintain a hierarchy of search spaces, where
the root of the tree is the space that was created when the search
goal closure was passed to the primitive function \texttt{try} for the
first time. This means that only the differences between the restored
space and the current search space have to be saved.

Since variables, which are local to a search goal, do not affect
computations outside an encapsulated search, it is possible to update
the local bindings of search goal lazily, i.e. when entering an
encapsulated search with a different search continuation of the same
goal than used the last time before. In order to implement this lazy
update strategy, we keep a reference to the space whose bindings are
in effect for every such tree of search spaces. For simplicity we add
this pointer to the search space nodes, but actually it will be used
only on the root space.\footnote{The reason for this double
indirection is that the root of search space may change -- when a
search continuation is restored, the current space becomes a child
of the restored space and therefore its root must be changed to the
one of the restored space -- and that the current reference must be
shared among all members of a single tree. We could have used a
\texttt{Ref (Ref SearchSpace)} instead.}

Note that neither search contexts nor search spaces save the current
choice point. This is because no choice points will be created inside a
local space and therefore the current choice point will not
change.\footnote{Actually, it would be possible to implement search
contexts as a special kind of choice point, but this would require
to check the invariant that all ``normal'' choice points must above
the search contexts in the control stack. It simplifies the code if we
let the type system ensure this property.}
\begin{verbatim}

> data SearchContext =
>     IOContext
>   | GlobalContext
>   | SearchContext NodePtr NodePtr Integer DataStack ContStack ThreadQueue
>                   Trail SearchContext SearchSpace

> data SearchSpace =
>     GlobalSpace
>   | LocalSpace { spaceId :: Integer,
>                  root :: Ref SearchSpace,
>                  parent :: Ref SearchSpace,
>                  trail :: Trail,
>                  script :: Trail,
>                  active :: Ref SearchSpace }

> instance Eq SearchSpace where
>   GlobalSpace == GlobalSpace  = True
>   GlobalSpace == LocalSpace _ _ _ _ _ _ = False
>   LocalSpace _ _ _ _ _ _ == GlobalSpace = False
>   LocalSpace id1 _ _ _ _ _ == LocalSpace id2 _ _ _ _ _ = id1 == id2

> instance Show SearchContext where
>   showsPrec p IOContext = showString "IOContext"
>   showsPrec p GlobalContext = showString "GlobalContext"
>   showsPrec p (SearchContext goal var tid ds rs rq tp sc ss) =
>     showParen (p >= 10) $
>     showString "SearchContext " . showsPrec 10 goal . showChar ' ' .
>       showsPrec 10 var . showChar ' ' . shows tid . showChar ' ' .
>         shows ds . showChar ' ' . shows rs . showChar ' ' . shows rq .
>           showChar ' ' . shows tp . showChar ' ' . showsPrec 10 sc .
>             showChar ' ' . showsPrec 10 ss

> instance Show SearchSpace where
>   showsPrec p GlobalSpace = showString "GlobalSpace"
>   showsPrec p (LocalSpace id _ _ _ _ _) = showParen (p >= 10) $
>     showString "LocalSpace " . shows id . showString " ..."

\end{verbatim}

\subsubsection{Constraints}
At present, the abstract machine supports equality and disequality
constraints. Equality constraints involving variables are implemented
by binding the variable to a term, disequality constraints by
collecting a list of terms at the variable.
\begin{verbatim}

> data Constraint = DisEq NodePtr deriving Show

\end{verbatim}

\subsubsection{The Trail}
The trail is used for saving the old value of a node when it is
overwritten as well when the state of a thread surrogate is
changed. During backtracking or when switching between search spaces
the old state of the computation may be recovered with the help of the
trail. We will simply save the whole node here. In a real
implementation only the updated field and its value need to be saved.
\begin{verbatim}

> type Trail = [UpdateInfo]
> data UpdateInfo =
>     NodeBinding NodePtr Node
>  | ThreadState ThreadPtr (Maybe Thread)
>  deriving Show

\end{verbatim}
