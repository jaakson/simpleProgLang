module Oblig12013

where

import Data.List
import Data.Char -- gives isDigit :: Char -> Bool

data AST = Leaf Integer | Var Char | FVar Char | Min AST | Sum AST AST | Mul AST AST
						| Con AST AST AST | Let AST AST AST | Fun AST AST AST
 						| Letfun AST AST AST AST AST deriving (Eq,Show)

-- Memory states used for evaluation in 'statevali'.
type VarState = [(AST,Integer)] -- [(variable, value)]
type FunState = [(AST,AST,AST,AST)] -- [(fnvariable, variable, variable, fndefinition)]

parse :: String -> AST
-- parses a string; returns the abstract syntax tree.
parse s = tree where (tree,list) = ast (tokens s)

tokens :: String -> [String]
-- divides list of tokens before the main processing begins.
tokens [] = []
tokens (' ':xs) = tokens xs
tokens (',':xs) = ",":tokens xs
tokens ('-':xs) = "-":tokens xs
tokens ('(':xs) = "(":tokens xs
tokens (')':xs) = ")":tokens xs
tokens ('*':xs) = "*":tokens xs
tokens ('+':xs) = "+":tokens xs
tokens ('=':xs) = "=":tokens xs 
tokens ('i':'f':xs) = "if":tokens xs
tokens ('i':'n':xs) = "in":tokens xs
tokens ('l':'e':'t':'f':'u':'n':xs) = "letfun":tokens xs
tokens ('l':'e':'t':xs) = "let":tokens xs
tokens ('t':'h':'e':'n':xs) = "then":tokens xs
tokens ('e':'l':'s':'e':xs) = "else":tokens xs
tokens (x:xs) = if (isDigit x) then (takeWhile isDigit (x:xs):tokens (dropWhile isDigit xs))
				else if (isVar x) then [x]:tokens xs
				else if (isFVar x) then [x]:tokens xs
				else error "Unexpected character."

isVar :: Char -> Bool
-- used in tokens, ast.
isVar c = elem c ['a' .. 'z']

isFVar :: Char -> Bool
-- used in tokens, ast.
isFVar c = elem c ['A' .. 'Z']

ast :: [String] -> (AST, [String])
-- sends strings to appropriate parsers.
ast ("-":xs) = astMin xs
ast ("+":xs) = astSum xs
ast ("*":xs) = astMul xs
ast ("if":xs)  = astCon xs
ast ("let":xs) = astLet xs
ast ("letfun":xs) = astLetfun xs 
ast (x:xs) = if (isDigit (head x)) then astInt (x:xs)
			 else if (isVar (head x)) then astVar (x:xs)
			 else if (isFVar (head x)) && xs == [] then astFVar [x]
			 else if (isFVar (head x)) && head xs == "(" then astFun (x:xs)
			 else error "Unexpected character." 

-- parsers for each kind of expression.
astInt :: [String] -> (AST,[String])
astInt (x:xs) = (Leaf (readAsInteger x),xs)

astVar :: [String] -> (AST,[String])
astVar (x:xs) = let y = head x in (Var y, xs)

astFVar :: [String] -> (AST,[String])
astFVar (x:xs) = let y = head x in (FVar y, xs)

astMin :: [String] -> (AST,[String])
astMin xs = let (term,end) = ast xs in (Min term, end)

astSum :: [String] -> (AST,[String])
astSum ("(":xs) = let (term1,left1) = ast xs in
				 (let (term2,left2) = ast (tail left1) in
				 (Sum term1 term2, tail left2))

astMul :: [String] -> (AST,[String])
astMul ("(":xs) = let (fac1,left1) = ast xs in
				 (let (fac2,end) = ast (tail left1) in
				 (Mul fac1 fac2, tail end))

astCon :: [String] -> (AST,[String])
astCon xs = let (test,left1) = ast xs in
		   (let (conseq1,left2) = ast (tail left1) in
		   (let (conseq2,end) = ast (tail left2) in
		   (Con test conseq1 conseq2, end)))

astLet :: [String] -> (AST,[String])
astLet (v:e:xs) = let (vari,empty) = ast [v] in 
				 (let (expr1,left1) = ast xs in
				 (let (expr2,end) = ast (tail left1) in
				 (Let vari expr1 expr2, end)))

astFun :: [String] -> (AST,[String])
astFun (x:p:xs) = let (funvar,left0) = ast [x] in 
				  let (expr1,left1) = ast xs in
				  let (expr2,left2) = ast (tail left1) in
				  ((Fun funvar expr1 expr2), tail left2)

astLetfun :: [String] -> (AST,[String])
astLetfun (f:x:y:e:xs) = let (funvar,fs) = ast [f] in
						 let (var1,vs) = ast [x] in
						 let (var2,ws) = ast [y] in
						 let (expr1,left1) = ast xs in
						 let (expr2,left2) = ast (tail left1) in
						 (Letfun funvar var1 var2 expr1 expr2, left2)

readAsInteger :: String -> Integer
-- used in astInt.
readAsInteger s = read s :: Integer

print :: AST -> String 
print (Leaf x) = show x
print (Min term) = "-" ++ Oblig12013.print term 
print (Sum term1 term2) = "(" ++ Oblig12013.print term1 ++ "+" ++ Oblig12013.print term2 ++ ")" 
print (Mul fac1 fac2) = "(" ++ Oblig12013.print fac1 ++ "*" ++ Oblig12013.print fac2 ++ ")"

evali :: AST -> Integer
-- Integer evaluation.  Calls the helper function statevali, which makes use of memory states.
evali tree = statevali tree [] []

statevali :: AST -> VarState -> FunState -> Integer
-- Integer evaluation.
statevali (Leaf x) vs fs = x
statevali (Var x) (v:vs) fs = let (vari,value) = v in
						      if vari == (Var x) then value else statevali (Var x) vs fs
statevali (Min term) vs fs = - (statevali term vs fs)
statevali (Sum term1 term2) vs fs = (statevali term1 vs fs) + (statevali term2 vs fs)
statevali (Mul fac1 fac2) vs fs = (statevali fac1 vs fs) * (statevali fac2 vs fs)
statevali (Con test conseq1 conseq2) vs fs = if (statevali test vs fs > 0)
											 then statevali conseq1 vs fs
										     else statevali conseq2 vs fs
statevali (Let vari expr1 expr2) vs fs = let value = statevali expr1 vs fs in 
									     let v = (vari,value) in statevali expr2 (v:vs) fs
statevali (Fun funvar arg1 arg2) vs (f:fs) = let (stateFunvar,v1,v2,fundef) = f in
											 if funvar == stateFunvar then
											 	let value1 = statevali arg1 vs fs in
											 	let value2 = statevali arg2 vs fs in
											 	statevali fundef ((v1,value1):(v2,value2):vs) (f:fs)
											 else statevali (Fun funvar arg1 arg2) vs fs
statevali (Letfun funvar var1 var2 expr1 expr2) vs fs = let newFunstate = (funvar,var1,var2,expr1) in
														statevali expr2 vs (newFunstate:fs)

-- Section 6, factorial function:
-- "letfun F x y = if +(x,-1) then *(x,F(+(x,-1),0)) else 1 in F(13,0)"

evalb :: AST -> Bool
-- Bolean evaluation.
evalb (Leaf x) = (x `mod` 2) == 1
evalb (Min term) = not (evalb term)
evalb (Sum term1 term2) = (evalb term1) || (evalb term2)
evalb (Mul fac1 fac2) = (evalb fac1) && (evalb fac2)

-- Section 3.3.2 example:
-- We cannot define evalb in terms of evali (as discussed in the exercise) for reasons like
-- the following: running evali on (Min (Leaf 1)) gives the output -1 (and -1 == 1 mod 2).
-- Since evalb on (Min (Leaf 1)) should give the output False, evalb (Min (Leaf 1)) gives
-- the opposite truth value of evalb (evali (Min (Leaf 1)) `mod` 2).

ev :: (AST -> t) -> String -> t
-- Higher-order evaluation
ev evaluator s = evaluator (parse s)
