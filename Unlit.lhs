% -*- LaTeX -*-
% $Id: Unlit.lhs 2676 2008-04-22 13:10:38Z wlux $
%
% Copyright (c) 2000-2008, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Unlit.lhs}
\section{Literate Comments}
Since version 0.7 of the language report, Curry accepts literate
source programs. In a literate source all program lines must begin
with a \verb|>| character in the first column. All other lines are
assumed to be documentation. In order to avoid some common errors with
literate programs, Curry requires at least one program line to be
present in the file. In addition, every block of program code must be
preceded and followed by a blank line.

Besides this ``traditional'' literate style, which was adopted from
Haskell, we also support Haskell's alternative style where the program
text is enclosed with lines starting with \verb|\begin{code}| and
\verb|\end{code}|, respectively. It is possible but not recommended to
mix both styles in the same file.

The module \texttt{Unlit} acts as a preprocessor which converts
literate source programs into the ``un-literate'' format accepted by
the lexer. The implementation, together with the comments below, was
derived from appendix C in the Haskell 1.2 report.
\begin{verbatim}

> module Unlit(unlit) where
> import Char
> import List
> import Position

\end{verbatim}
Each line of a literate script is either a program line, one of the
delimiters \verb|\begin{code}| and \verb|\end{code}|, a blank line, or
a comment line. In the first case the text is kept with the line.
\begin{verbatim}

> data Classified = Program String | BeginCode | EndCode | Blank | Comment

\end{verbatim}
In a literate program, all lines between the \verb|\begin{code}| and
\verb|\end{code}| delimiters and all other lines starting with a
\verb|>| character are program lines. The remaining lines are either
blank lines, containing only white space, or comment lines. The
function \texttt{classify} below classifies a single program line. Its
first argument is a flag that denotes whether that line belongs to a
code block between \verb|\begin{code}| and \verb|\end{code}|
delimiters. The boolean flag returned together with the classified
line denotes whether the next line belongs to a code block. The
leading \verb|>| character of program lines outside code blocks is
replaced by a single space in order to preserve tab alignments.
\begin{verbatim}

> classify :: Bool -> String -> (Bool,Classified)
> classify True  cs =
>   if "\\end{code}" `isPrefixOf` cs then (False,EndCode)
>   else (True,Program cs)
> classify False ""      = (False,Blank)
> classify False (c:cs)
>   | c == '>'           = (False,Program (' ':cs))
>   | c == '\\'          =
>       if "begin{code}" `isPrefixOf` cs then (True,BeginCode)
>       else (False,Comment)
>   | all isSpace (c:cs) = (False,Blank)
>   | otherwise          = (False,Comment)

\end{verbatim}
In the transformed source only the contents of program lines is
retained.
\begin{verbatim}

> unclassify :: Classified -> String
> unclassify (Program cs) = cs
> unclassify BeginCode    = ""
> unclassify EndCode      = ""
> unclassify Blank        = ""
> unclassify Comment      = ""

\end{verbatim}
The main function of this module processes a literate program into
error messages (if any) and the corresponding non-literate program.
\begin{verbatim}

> unlit :: FilePath -> String -> (String,String)
> unlit fn lcy = (es,cy)
>   where (_,cs) = mapAccumL classify False (lines lcy)
>         es = unlines (errors fn cs)
>         cy = unlines (map unclassify cs)

\end{verbatim}
Check that each program line is not adjacent to a comment line, the
last code block is terminated with \verb|\end{code}|, and there is at
least one program line or one (possibly empty) code block.
\begin{verbatim}

> errors :: FilePath -> [Classified] -> [String]
> errors fn cs =
>   concat (zipWith adjacent cs' (tail cs')) ++
>   if null ds then empty p0 (filter isProgram cs)
>   else [last ds | odd (length ds)]
>   where p0 = first fn
>         cs' = zipWith P (iterate nl p0) cs
>         ds = delims cs'

\end{verbatim}
Given a line number and a pair of adjacent lines, generate a list of
error messages, which will contain either one entry or none. Note that
blank lines are not required after the \verb|\begin{code}| and before
the \verb|\end{code}| delimiters.
\begin{verbatim}

> adjacent :: P Classified -> P Classified -> [String]
> adjacent (P _ (Program _)) (P p Comment    ) = [message p "after"]
> adjacent (P _ (Program _)) (P p BeginCode  ) = [message p "after"]
> adjacent (P p EndCode    ) (P _ (Program _)) = [message p "before"]
> adjacent (P p Comment    ) (P _ (Program _)) = [message p "before"]
> adjacent _                 _                 = []

> message p w = atP p ("comment line " ++ w ++ " program line.")

\end{verbatim}
Given the list of program lines report an error if this list is empty.
\begin{verbatim}

> empty :: Position -> [Classified] -> [String]
> empty p cs = [atP p "no code in literate script" | null cs]

> isProgram :: Classified -> Bool
> isProgram (Program _) = True
> isProgram _           = False

\end{verbatim}
If a literate program uses \verb|\begin{code}| and \verb|\end{code}|
delimiters, we make sure that the last code block is closed. The
following function associates an error message with every delimiter,
but an error is reported only if the number of delimiters is odd.
\begin{verbatim}

> delims :: [P Classified] -> [String]
> delims cs = [atP p "missing \\end{code}" | P p c <- cs, isDelim c]

> isDelim :: Classified -> Bool
> isDelim BeginCode = True
> isDelim EndCode   = True
> isDelim _         = False

\end{verbatim}
