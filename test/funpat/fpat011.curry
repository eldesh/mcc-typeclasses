-- This is example 2 from Antoy, Hanus. Programming with Function Patterns.

data Exp = Lit Int | Var [Char] | Add Exp Exp | Mul Exp Exp

evalTo e = Add (Lit 0) e
         ? Add e (Lit 0)
	 ? Mul (Lit 1) e
	 ? Mul e (Lit 1)

replace _ [] x = x
replace (Add l r) (1:p) x = Add (replace l p x) r
replace (Add l r) (2:p) x = Add l (replace r p x)
replace (Mul l r) (1:p) x = Mul (replace l p x) r
replace (Mul l r) (2:p) x = Mul l (replace r p x)

simplify (replace c p (evalTo x)) = replace c p x

varInExp (replace c p (Var v)) = v

-- Main function

fullSimplify t =
  case findall (\t' -> t' =:= simplify t) of
    [] -> t
    (t:ts) -> foldr1 (?) (map fullSimplify (t:ts))

goal t = t =:= fullSimplify (Mul (Lit 1) (Add (Var "x") (Lit 0)))
