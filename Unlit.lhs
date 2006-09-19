% -*- LaTeX -*-
% $Id: Unlit.lhs 1783 2005-10-06 20:35:55Z wlux $
%
% Copyright (c) 2000-2005, Wolfgang Lux
% See LICENSE for the full license.
%
\nwfilename{Unlit.lhs}
\section{Literate Comments}
Since version 0.7 of the language report, Curry accepts literate
source programs. In a literate source all program lines must begin
with a greater sign in the first column. All other lines are assumed
to be documentation. In order to avoid some common errors with
literate programs, Curry requires at least one program line to be
present in the file. In addition, every block of program code must be
preceded by a blank line and followed by a blank line.

The module \texttt{Unlit} acts as a preprocessor which converts
literate source programs into the ``un-literate'' format accepted by
the lexer. The implementation, together with the comments below, was
derived from appendix D in the Haskell 1.2 report.
\begin{verbatim}

> module Unlit(unlit) where
> import Char
> import Position

\end{verbatim}
Each of the lines in a literate script is a program line, a blank
line, or a comment line. In the first case the text is kept with the
line.
\begin{verbatim}

> data Classified = Program String | Blank | Comment

\end{verbatim}
In a literate program, program lines begin with a \verb|>| character,
blank lines contain only whitespace, and all other lines are comment
lines.
\begin{verbatim}

> classify :: String -> Classified
> classify ""            = Blank
> classify (c:cs)
>   | c == '>'           = Program cs
>   | all isSpace (c:cs) = Blank
>   | otherwise          = Comment

\end{verbatim}
In the corresponding program, program lines have the leading \verb|>|
replaced by a leading space, to preserve tab alignments.
\begin{verbatim}

> unclassify :: Classified -> String
> unclassify (Program cs) = ' ' : cs
> unclassify Blank        = ""
> unclassify Comment      = ""

\end{verbatim}
Process a literate program into error messages (if any) and the
corresponding non-literate program.
\begin{verbatim}

> unlit :: FilePath -> String -> (String,String)
> unlit fn lcy = (es,cy)
>   where cs = map classify (lines lcy)
>         es = unlines (errors fn cs)
>         cy = unlines (map unclassify cs)

\end{verbatim}
Check that each program line is not adjacent to a comment line and
there is at least one program line.
\begin{verbatim}

> errors :: FilePath -> [Classified] -> [String]
> errors fn cs =
>   concat (zipWith3 adjacent (iterate nl (first fn)) cs (tail cs)) ++
>   empty fn (filter isProgram cs)

\end{verbatim}
Given a line number and a pair of adjacent lines, generate a list of
error messages, which will contain either one entry or none.
\begin{verbatim}

> adjacent :: Position -> Classified -> Classified -> [String]
> adjacent p (Program _) Comment     = [message (nl p) "after"]
> adjacent p Comment     (Program _) = [message p "before"]
> adjacent p _           _           = []

> message p w = atP p ("comment line " ++ w ++ " program line.")

\end{verbatim}
Given the list of program lines generate an error if this list is
empty.
\begin{verbatim}

> empty :: FilePath -> [Classified] -> [String]
> empty fn cs = [atP (first fn) ("no code in literate script") | null cs]

> isProgram :: Classified -> Bool
> isProgram (Program _) = True
> isProgram _ = False

\end{verbatim}
