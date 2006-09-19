% -*- LaTeX -*-
% $Id: CElim.lhs 1822 2005-11-07 22:50:22Z wlux $
%
% Copyright (c) 2003-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{CElim.lhs}
\subsection{Eliminating unused variables}
\begin{verbatim}

> module CElim(elimUnused) where
> import CCode
> import Set

\end{verbatim}
The code generation algorithm may insert unused variables into the
generated code. While these variables are discarded by the C compiler
-- at least when optimization is turned on -- we prefer to remove
these variables before actually emitting the code. This improves the
overall performance because our compiler does not have to emit this
code and the C compiler does not have to parse it.
\begin{verbatim}

> elimUnused :: [CStmt] -> [CStmt]
> elimUnused sts = snd (foldr elimUnusedVars (zeroSet,[]) sts)

> elimUnusedVars :: CStmt -> (Set String,[CStmt]) -> (Set String,[CStmt])
> elimUnusedVars (CLocalVar ty v e) (vs,sts)
>   | v `elemSet` vs =
>       (maybe id usedVars e $ deleteFromSet v vs,CLocalVar ty v e : sts)
>   | otherwise = (vs,sts)
> elimUnusedVars (CStaticArray ty v init) ~(vs,sts) =
>   (vs,CStaticArray ty v init : sts)
> elimUnusedVars (CppCondStmts c sts1 sts2) ~(vs,sts) =
>   (vs1 `unionSet` vs2,CppCondStmts c sts1' sts2' : sts)
>   where (vs1,sts1') = foldr elimUnusedVars (vs,[]) sts1
>         (vs2,sts2') = foldr elimUnusedVars (vs,[]) sts2
> elimUnusedVars (CBlock sts) ~(vs,sts') =
>   (vs' `unionSet` vs,CBlock sts'' : sts')
>   where (vs',sts'') = foldr elimUnusedVars (zeroSet,[]) sts
> elimUnusedVars (CAssign v e) ~(vs,sts) =
>   (usedLVars v (usedVars e vs),CAssign v e : sts)
> elimUnusedVars (CIncrBy v e) ~(vs,sts) =
>   (usedLVars v (usedVars e vs),CIncrBy v e : sts)
> elimUnusedVars (CDecrBy v e) ~(vs,sts) =
>   (usedLVars v (usedVars e vs),CDecrBy v e : sts)
> elimUnusedVars (CProcCall f es) ~(vs,sts) =
>   (foldr usedVars vs (CExpr f:es),CProcCall f es : sts)
> elimUnusedVars (CIf e sts1 sts2) ~(vs,sts) =
>   (usedVars e (vs1 `unionSet` vs2 `unionSet` vs),CIf e sts1' sts2' : sts)
>   where (vs1,sts1') = foldr elimUnusedVars (zeroSet,[]) sts1
>         (vs2,sts2') = foldr elimUnusedVars (zeroSet,[]) sts2
> elimUnusedVars (CSwitch e cases) ~(vs,sts) =
>   (usedVars e (foldr unionSet vs vss),CSwitch e cases' : sts)
>   where (vss,cases') = unzip (map elimUnusedCaseVars cases)
>         elimUnusedCaseVars (CCase c sts) = (vs,CCase c sts')
>           where (vs,sts') = foldr elimUnusedVars (zeroSet,[]) sts
>         elimUnusedCaseVars (CDefault sts) = (vs,CDefault sts')
>           where (vs,sts') = foldr elimUnusedVars (zeroSet,[]) sts
> elimUnusedVars (CLoop sts) ~(vs,sts') =
>   (vs' `unionSet` vs,CLoop sts'' : sts')
>   where (vs',sts'') = foldr elimUnusedVars (zeroSet,[]) sts
> elimUnusedVars CBreak ~(vs,sts) = (vs,CBreak : sts)
> elimUnusedVars CContinue ~(vs,sts) = (vs,CContinue : sts)
> elimUnusedVars (CReturn e) ~(vs,sts) = (usedVars e vs,CReturn e : sts)
> elimUnusedVars (CLabel l) ~(vs,sts) = (vs,CLabel l : sts)
> elimUnusedVars (CGoto l) ~(vs,sts) = (vs,CGoto l : sts)

> usedLVars :: LVar -> Set String -> Set String
> usedLVars (LVar v) vs = addToSet v vs
> usedLVars (LElem e1 e2) vs = usedLVars e1 (usedVars e2 vs)
> usedLVars (LField e _) vs = usedLVars e vs

> usedVars :: CExpr -> Set String -> Set String
> usedVars CNull vs = vs
> usedVars (CInt _) vs = vs
> usedVars (CFloat _) vs = vs
> usedVars (CString _) vs = vs
> usedVars (CElem e1 e2) vs = usedVars e1 (usedVars e2 vs)
> usedVars (CField e _) vs = usedVars e vs
> usedVars (CFunCall f es) vs = foldr usedVars vs (CExpr f:es)
> usedVars (CCond e1 e2 e3) vs = usedVars e1 (usedVars e2 (usedVars e3 vs))
> usedVars (CAdd e1 e2) vs = usedVars e1 (usedVars e2 vs)
> usedVars (CSub e1 e2) vs = usedVars e1 (usedVars e2 vs)
> usedVars (CMul e1 e2) vs = usedVars e1 (usedVars e2 vs)
> usedVars (CDiv e1 e2) vs = usedVars e1 (usedVars e2 vs)
> usedVars (CMod e1 e2) vs = usedVars e1 (usedVars e2 vs)
> usedVars (CShift e _) vs = usedVars e vs
> usedVars (CRel e1 _ e2) vs = usedVars e1 (usedVars e2 vs)
> usedVars (CAddr e) vs = usedVars e vs
> usedVars (CCast _ e) vs = usedVars e vs
> usedVars (CExpr x) vs = addToSet x vs

\end{verbatim}
