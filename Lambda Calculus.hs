data Expr = Var String | App Expr Expr | Abs String Expr | D Expr Expr | Sum [Expr] | Zero
instance Show Expr where show e = showL e 

--extraVars = [x++(show n) | x <- basicVars , n <- [1..99]]
basicVars = ["x","y","z","a","b","c","d","e","f","g","h","m","n","p","r","s","t","u","v","w"]
variablePool = basicVars 

-- Finds an unused variable in an expression	 
fresh :: [String] -> Expr -> String
fresh xs e = freshTool (xs++variablePool) e

freshTool :: [String] -> Expr -> String
freshTool (x:xs) e = if (elem x (vars e)) then (freshTool xs e) else x

vars :: Expr -> [String]
vars e = varsBuild False [] e

freeVars :: Expr -> [String]
freeVars e = varsBuild True [] e

varsBuild :: Bool -> [String] -> Expr -> [String]
varsBuild True xs (Abs x e) = delete x (varsBuild True xs e)
varsBuild False xs (Abs x e) = if (elem x xs) then (varsBuild False xs e) else (varsBuild False (x:xs) e)
varsBuild b xs (Var x) = if (elem x xs) then xs else (x:xs)
varsBuild b xs (App e1 e2) = varsBuild b (varsBuild b xs e1) e2

delete :: Eq a => a -> [a] -> [a]
delete a [] = []
delete a (x:xs) = if (a==x) then xs else x:(delete a xs)
--------------------------------------------

-- Alpha Conversion  
alphaConvert :: Expr -> [String] -> String -> Expr
alphaConvert e xs s = alphaConvertTool False e s (fresh xs e)

alphaConvertTool :: Bool -> Expr -> String -> String -> Expr
alphaConvertTool b (App e1 e2) s t = App (alphaConvertTool b e1 s t) (alphaConvertTool b e2 s t)
alphaConvertTool b (Abs x e) s t = if x == s then (Abs t (alphaConvertTool True e s t)) else (Abs x (alphaConvertTool b e s t))
--Not bound by s yet
alphaConvertTool False e s t = e
--Inside an s binding
alphaConvertTool True (Var x) s t = if x == s then (Var t) else (Var x)
--------------------

-- Checks whether a given expression is in BNF
betaNormalForm :: Expr -> Bool
betaNormalForm (Var x) = True
betaNormalForm (Abs s e) = betaNormalForm e
betaNormalForm (App (Abs s e1) e2) = False
betaNormalForm (App e1 e2) = (betaNormalForm e1) || (betaNormalForm e2)


--One step beta reduction
betaReduction :: Expr -> Expr
betaReduction e = betaReductionTool [] e

betaReductionTool :: [String] -> Expr -> Expr
betaReductionTool ys (Var x) = Var x
betaReductionTool ys (Abs x e) = Abs x (betaReductionTool (x:ys) e)
betaReductionTool ys (App (Abs s e1) e2) = substituteCaptureAvoid ys e1 s e2
betaReductionTool ys (App e1 e2) = if (betaNormalForm e1) then App e1 (betaReductionTool ys e2) else App (betaReductionTool ys e1) e2


-- Substitution (e[s/x])
substitute :: Expr -> String -> Expr -> Expr
substitute (Var x) s e = if x == s then e else (Var x)
substitute (App e1 e2) s e = App (substitute e1 s e) (substitute e2 s e)
substitute (Abs t e1) s e = if t == s then (Abs t e1) else (Abs t (substitute e1 s e))

substituteCaptureAvoid :: [String] -> Expr -> String -> Expr -> Expr
substituteCaptureAvoid ys (Var x) y e = if (x==y) then e else (Var x)
substituteCaptureAvoid ys (App e1 e2) x e = App (substituteCaptureAvoid ys e1 x e) (substituteCaptureAvoid ys e2 x e)
substituteCaptureAvoid ys (Abs x e1) y e = if (x==y) then (Abs x e1) else if (elem x (freeVars e)) then (substituteCaptureAvoid ys (alphaConvert (Abs x e1) ys x) y e) else (Abs x (substituteCaptureAvoid ys e1 y e))

-- Differential substitution
diffSub :: Expr -> String -> Expr -> Expr
diffSub (Var y) x e = if (y==x) then e else (Sum [])
--diffSub (Abs y s) x e = 
diffSub (App e1 e2) x e = Sum [(App (diffSub e1 x e) e2) , (App (D e1 (diffSub e2 x e)) e2 )]
diffSub (D e1 e2) x e = Sum [(D (diffSub e1 x e) e2) , (D e1 (diffSub e2 x e))]
diffSub (Sum []) x e = Sum []
diffSub (Sum ys) x e = Sum (map (\y -> diffSub y x e) ys) 

--Logical terms
tL = Abs "x" (Abs "y" (Var "x"))
fL = Abs "x" (Abs "y" (Var "y"))

andL = Abs "a" (Abs "b" (App (App (Var "a") (Var "b")) fL))
orL = Abs "a" (Abs "b" (App (App (Var "a") tL) (Var "b")))
notL = Abs "a" (App (App (Var "a") fL) tL)

ifThenElseL = Abs "x" (Var "x")

--Fixed Points (fpL F = n s.t. n = Fn)
turingHalf = Abs "x" (Abs "y" (App (Var "y") (App (App (Var "x") (Var "x")) (Var "y"))))
fpL = App turingHalf turingHalf

--Printing expressions
showL :: Expr -> String
showL Zero = "0"
showL (Var x) = x
showL (Abs x e) = "L"++x++"."++(showL e)
showL (App (Var x) (Var y)) = x++y
showL (App (Var x) e) = x++"("++(showL e)++")"
showL (App e (Var y))  = "("++(showL e)++")"++y
showL (App e1 e2) = "("++(showL e1)++")("++(showL e2)++")"

--Reading expressions
readL :: String -> Expr -- abstactions in brackets don't work
readL s = readLTool s

readLTool :: String -> Expr
readLTool "" = Zero
readLTool s = if ((take 1 s)=="L") then (buildAbs (tail s)) else (buildApp(reverse s) "")

--Dealing with abstractions
buildAbs :: String -> Expr
buildAbs s = buildAbsStart "" s

buildAbsStart :: String -> String -> Expr
buildAbsStart ys (x:xs) = if x == '.' then (buildAbsEnd (extractVars ys) xs) else (buildAbsStart (ys++[x]) xs)

buildAbsEnd :: [String] -> String -> Expr
buildAbsEnd [] s2 = readLTool s2
buildAbsEnd (x:xs) s2 = Abs x (buildAbsEnd xs s2)

--Dealing with applications
buildApp :: String -> String -> Expr
buildApp "" s2 = buildAppChain (reverse (extractVars s2))
buildApp (x:xs) s2 = if (x==')') then splitApp 0 1 xs s2 else buildApp xs (x:s2)

splitApp :: Int -> Int -> String -> String -> Expr 
splitApp l r "" s2 = if (l==r) then (buildApp (reverse s2) "") else error "Mismatched brackets"
splitApp l r (x:xs) s2 = if (l==r) then (App (readLTool (reverse (x:xs))) (readLTool s2)) else (if (x=='(') then (splitApp (l+1) r xs s2) else (if (x==')') then (splitApp l (r+1) xs s2) else splitApp l r xs (x:s2)))

buildAppChain :: [String] -> Expr
buildAppChain [] = Zero
buildAppChain [x] = Var x
buildAppChain (x:xs) = App (buildAppChain  xs) (Var x)

-- Separate all variables in a list of variables
extractVars :: String -> [String]
extractVars "" = []
extractVars [x] = if (elem [x] basicVars) then [[x]] else error "Not a well-formed expression"
extractVars [x,y] = if (elem [x] basicVars) then (if (elem [y] basicVars) then [[x],[y]] else (if (elem [y] (map show [1..9])) then [x:[y]] else (error "Not a well-formed expression"))) else error "Not a well-formed expression"
extractVars (x:y:z:xs) = if (elem [x] basicVars) then (if (elem [y] basicVars) then ([x]: extractVars(y:z:xs)) else (if (elem [z] basicVars) then ((x:[y]):(extractVars (z:xs))) else ((x:y:[z]):(extractVars xs)))) else error "Not a well-formed expression"