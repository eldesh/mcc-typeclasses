-- $Id: Lexing.curry 2013 2006-11-16 14:10:51Z wlux $

-- Implementation of lexing combinators based on
-- Manuel M.T. Chakravarty. Lazy Lexing is Fast. In:
-- Proc. FLOPS '99, LNCS 1772, pp. 68--84

module Lexing(Position(..), Regexp, Lexer, LexerState, Action, Meta, OneToken,
	      epsilon, char, (+>), (>|<), (>||<), star, plus, quest,
	      alt, string, lexaction, lexmeta, ident, ctrlLexer,
	      execLexer, lexOne) where
import Maybe
import List

infixl 4 `star`, `plus`, `quest`
infixl 3 +>
infixl 2 >|<, >||<

-- Types
newtype Position  = P (String, Int, Int)
type LexerState s = (String, Position, s)

type Regexp s t	  = Lexer s t -> Lexer s t
data Lexer s t    = State (LexAction s t) [(Char, Lexer s t)]
type OneToken s t = (Maybe t, Lexer s t, LexerState s)

type Action t = String -> Position -> Maybe t
type Meta s t = Position -> s -> (Position, s, Maybe (Lexer s t))

data LexAction s t = Action (Action t) | Meta (Meta s t) | NoAction

instance Eq Position where
  P p1 == P p2 = p1 == p2
instance Ord Position where
  P p1 `compare` P p2 = p1 `compare` p2

-- Regular Expressions

epsilon :: Regexp s t
epsilon = id

char :: Char -> Regexp s t
char c = \l -> State NoAction [(c,l)]

(+>) :: Regexp s t -> Regexp s t -> Regexp s t
(+>) = (.)

(>|<) :: Regexp s t -> Regexp s t -> Regexp s t
re >|< re' = \l -> re l >||< re' l

star :: Regexp s t -> Regexp s t -> Regexp s t
re1 `star` re2 = self +> re2 where self = (re1 +> self >|< epsilon)

plus :: Regexp s t -> Regexp s t -> Regexp s t
re1 `plus` re2 = re1 +> (re1 `star` re2)

quest :: Regexp s t -> Regexp s t -> Regexp s t
re1 `quest` re2 = (re1 +> re2) >|< re2


alt :: [Char] -> Regexp s t
alt = foldr1 (>|<) . map char

string :: String -> Regexp s t
string = foldr (+>) epsilon . map char

ident :: Regexp s t
ident = letter +> (letter >|< digit) `star` epsilon
  where letter = alt (map chr ([ord 'a' .. ord 'z'] ++ [ord 'A' .. ord 'Z']))
	digit  = alt (map chr [ord '0' .. ord '9'])

-- Actions

lexaction :: Regexp s t -> Action t -> Lexer s t
lexaction re a = re (State (Action a) [])

(>||<) :: Lexer s t -> Lexer s t -> Lexer s t
State a cls >||< State a' cls' =
  State (joinActions a a') (accum (>||<) (cls ++ cls'))
  where
    accum _ []		  = []
    accum f ((c,l) : cls)
      | null cls1 = (c,l) : accum f cls2
      | otherwise = (c,foldr1 f (l : map snd cls1)) : accum f cls2
      where (cls1,cls2) = partition (\(c',_) -> c == c') cls

    joinActions a a' =
      case (a,a') of
        (NoAction,_) -> a'
        (_,NoAction) -> a
        _ -> error "Lexers: Ambiguous action!"


-- Meta Actions

lexmeta :: Regexp s t -> Meta s t -> Lexer s t
lexmeta re f = re (State (Meta f) [])

ctrlLexer :: Lexer s t
ctrlLexer = char '\n' `lexmeta` newline
       >||< char '\r' `lexmeta` newline
       >||< char '\f' `lexmeta` formfeed
       >||< char '\t' `lexmeta` tab
  where newline  (P (fname, row, _  )) s = (P (fname, row + 1, 1), s, Nothing)
	formfeed (P (fname, row, col)) s = (P (fname, row, col + 1), s, Nothing)
	tab      (P (fname, row, col)) s = (P (fname, row, col + 8 - col `mod` 8), s, Nothing)


-- Lexing

execLexer :: Lexer s t -> LexerState s -> [t]
execLexer l ([], _, _) = []
execLexer l state@(_:_, _, _) =
  case lexOne l state of
    (Nothing, l', state') -> execLexer l' state'
    (Just t,  l', state') -> t : execLexer l' state'

lexOne :: Lexer s t -> LexerState s -> (Maybe t, Lexer s t, LexerState s)
lexOne l state = collect l state id (error "Lexical error!")
  where
    collect (State a cls) state@(cs, pos, s) lexeme last =
      case cs of
        []      -> last'
        (c:cs') -> case lookup c cls of
		     Nothing -> last'
		     Just l' -> collect l' (cs', pos, s) (lexeme . (c:)) last'
      where last' = action a state lexeme last

    action NoAction   _            _      last = last
    action (Action a) (cs, pos, s) lexeme _    =
      (a (lexeme "") pos, l, (cs, advancePos pos (lexeme ""), s))
    action (Meta f)   (cs, pos, s) lexeme _    =
      (Nothing, fromMaybe l l', (cs, pos', s'))
      where (pos', s', l') = f (advancePos pos (lexeme "")) s

advancePos = foldr advance
  where advance c (P (fname, row, col)) =
          case c of
            '\n' -> P (fname, row + 1, 1)
            '\r' -> P (fname, row + 1, 1)
            '\t' -> P (fname, row, col + 8 - col `mod` 8)
            _    -> P (fname, row, col + 1)
