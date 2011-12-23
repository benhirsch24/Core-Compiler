module Parser where
import Language
import Data.Char (isSpace, isDigit, isAlpha, digitToInt)

type Token = String
type Parser a = [Token] -> [(a, [Token])]

clex :: String -> [(Int, Token)]
clex cs = clex' 1 cs

clex' :: Int -> String -> [(Int, Token)]
clex' _ [] = []
clex' n (c:cs)
   | c == '\n' = clex' (n+1) cs
   | isSpace c = clex' n cs
   | isDigit c = let num_token = c : takeWhile isDigit cs
                     rest_cs   = dropWhile isDigit cs
                 in  (n, num_token) : clex' n rest_cs
   | isAlpha c = let var_tok = c : takeWhile isIdChar cs
                     rest_cs = dropWhile isIdChar cs
                 in  (n, var_tok) : clex' n rest_cs
   | c == '|' = if head cs == '|'
                then clex' n $ dropWhile (\c -> not $ c == '\n') cs
                else (n, c : takeWhile isIdChar cs) : (clex' n $ dropWhile isIdChar cs)
   | c:[(head cs)] `elem` twoCharOps = (n, c:[(head cs)]) : (clex' n $ drop 1 cs)
   | otherwise = (n, [c]) : clex' n cs

twoCharOps :: [String]
twoCharOps = ["==", "-=", ">=", "<=", "->"]

arithOps :: [String]
arithOps = ["+", "-", "*", "/"]

relOps :: [String]
relOps = twoCharOps ++ ["<", ">"]

boolOps :: [String]
boolOps = ["&", "|"]

binOps :: [String]
binOps = relOps ++ arithOps ++ boolOps

isIdChar :: Char -> Bool
isIdChar c = isAlpha c || isDigit c || (c == '_')

pSat :: (String -> Bool) -> Parser String
pSat _ [] = []
pSat f (tok:toks)
   | f tok = [(tok, toks)]
   | otherwise = []

pLit :: String -> Parser String
pLit s = pSat (== s)

pVar :: Parser String
pVar = pSat satFun
   where
   satFun str@(c:cs) = isAlpha c && 
                       (not $ str `elem` keywords) && 
                       all (\h -> isAlpha h || isDigit h || h == '_') cs

keywords :: [String]
keywords = ["let", "letrec", "case", "in", "of" , "Pack"]

pNum :: Parser Int
pNum = pApply (pSat (all isDigit)) strToNum
   where strToNum s = read s :: Int

pAlt :: Parser a -> Parser a -> Parser a
pAlt p1 p2 toks = (p1 toks) ++ (p2 toks)

pThen :: (a -> b -> c) -> Parser a -> Parser b -> Parser c
pThen combine p1 p2 toks = 
   [ (combine v1 v2, toks2) | (v1, toks1) <- p1 toks, 
                              (v2, toks2) <- p2 toks1 ]

pThen3 :: (a -> b -> c -> d) -> Parser a -> Parser b -> Parser c -> Parser d
pThen3 combine pa pb pc toks =
   [ (combine v1 v2 v3, toks3) | (v1, toks1) <- pa toks,
                                 (v2, toks2) <- pb toks1,
                                 (v3, toks3) <- pc toks2 ]

pThen4 :: (a -> b -> c -> d -> e) -> Parser a -> Parser b -> Parser c -> Parser d -> Parser e
pThen4 combine pa pb pc pd toks =
   [ (combine v1 v2 v3 v4, toks4) | (v1, toks1) <- pa toks,
                                 (v2, toks2) <- pb toks1,
                                 (v3, toks3) <- pc toks2,
                                 (v4, toks4) <- pd toks3 ]

pThen5 :: (a -> b -> c -> d -> e -> f) -> Parser a -> Parser b -> Parser c -> Parser d -> Parser e -> Parser f
pThen5 combine pa pb pc pd pe toks =
   [ (combine v1 v2 v3 v4 v5, toks5) | (v1, toks1) <- pa toks,
                                 (v2, toks2) <- pb toks1,
                                 (v3, toks3) <- pc toks2,
                                 (v4, toks4) <- pd toks3,
                                 (v5, toks5) <- pe toks4 ]

pThen6 :: (a -> b -> c -> d -> e -> f -> g) -> Parser a -> Parser b -> Parser c -> Parser d -> Parser e -> Parser f -> Parser g
pThen6 combine pa pb pc pd pe pf toks =
   [ (combine v1 v2 v3 v4 v5 v6, toks6) | (v1, toks1) <- pa toks,
                                 (v2, toks2) <- pb toks1,
                                 (v3, toks3) <- pc toks2,
                                 (v4, toks4) <- pd toks3,
                                 (v5, toks5) <- pe toks4,
                                 (v6, toks6) <- pf toks5 ]

pZeroOrMore :: Parser a -> Parser [a]
pZeroOrMore p = (pOneOrMore p) `pAlt` (pEmpty [])

pEmpty :: a -> Parser a
pEmpty v toks = [(v, toks)]

-- ([Token] -> [(a, [Token])]) -> [Token] -> [(a, [Token])]
pOneOrMore :: Parser a -> Parser [a]
pOneOrMore p toks = pThen (:) p (pZeroOrMore p) toks

pApply :: Parser a -> (a -> b) -> Parser b
pApply p f toks = [ (f v, toks1) | (v, toks1) <- p toks]

pOneOrMoreWithSep :: Parser a -> Parser b -> Parser [a]
pOneOrMoreWithSep pa pb = pThen (:) pa sepAndParse
   where sepAndParse = (pThen3 (\b a la -> a:la) pb pa sepAndParse) `pAlt` (pEmpty [])


syntax :: [Token] -> CoreProgram
syntax = take_first_parse . pProgram
   where
   take_first_parse ((prog, []) : rest) = prog
   take_first_parse (parse      : rest) = take_first_parse rest
   take_first_parse _                   = error "Syntax error"

pProgram :: Parser CoreProgram
pProgram = pOneOrMoreWithSep pSc (pLit ";")

pSc :: Parser CoreScDefn
pSc = pThen4 mk_sc pVar (pZeroOrMore pVar) (pLit "=") pExpr

mk_sc :: String -> [String] -> String -> CoreExpr -> CoreScDefn
mk_sc name vars eq expr = (name, vars, expr)

pExpr :: Parser CoreExpr
pExpr = pThen4 mkLet (pLit "let" `pAlt` pLit "letrec") pDefns (pLit "in") pExpr
        `pAlt` pThen4 mkCase (pLit "case") pExpr (pLit "of") pAlts
        `pAlt` pThen4 mkLambda (pLit "\\") (pOneOrMore pVar) (pLit ".") pExpr
        `pAlt` pExpr1

pExpr1 :: Parser CoreExpr
pExpr1 = pThen assembleOp pExpr2 pExpr1c

pExpr1c :: Parser PartialExpr
pExpr1c = (pThen FoundOp (pLit "|") pExpr1) `pAlt` (pEmpty NoOp)

pExpr2 :: Parser CoreExpr
pExpr2 = pThen assembleOp pExpr3 pExpr2c

pExpr2c :: Parser PartialExpr
pExpr2c = (pThen FoundOp (pLit "&") pExpr2) `pAlt` (pEmpty NoOp)

pExpr3 :: Parser CoreExpr
pExpr3 = pThen assembleOp pExpr4 pExpr3c

pExpr3c :: Parser PartialExpr
pExpr3c = (pThen FoundOp (pSat (\s -> s `elem` relOps)) pExpr4) `pAlt` (pEmpty NoOp)

pExpr4 :: Parser CoreExpr
pExpr4 = pThen assembleOp pExpr5 pExpr4c

pExpr4c :: Parser PartialExpr
pExpr4c = (pThen FoundOp (pLit "+") pExpr4) `pAlt` (pThen FoundOp (pLit "-") pExpr5) `pAlt` (pEmpty NoOp)

pExpr5 :: Parser CoreExpr
pExpr5 = pThen assembleOp pExpr6 pExpr5c

pExpr5c :: Parser PartialExpr
pExpr5c = (pThen FoundOp (pLit "*") pExpr5) `pAlt` (pThen FoundOp (pLit "/") pExpr6) `pAlt` (pEmpty NoOp)

pExpr6 :: Parser CoreExpr
pExpr6 = (pOneOrMore pAExpr) `pApply` mk_ap_chain

assembleOp :: CoreExpr -> PartialExpr -> CoreExpr
assembleOp e1 NoOp = e1
assembleOp e1 (FoundOp op e2) = EAp (EAp (EVar op) e1) e2

mk_ap_chain :: [CoreExpr] -> CoreExpr
mk_ap_chain exprs = foldl EAp (head exprs) (tail exprs)

mkLambda :: String -> [Name] -> String -> CoreExpr -> CoreExpr
mkLambda _ vars _ expr = ELam vars expr

mkCase :: String -> CoreExpr -> String -> [CoreAlt] -> CoreExpr
mkCase _ guard _ alts = ECase guard alts

pAlts :: Parser [CoreAlt]
pAlts = pOneOrMoreWithSep (pThen6 mkAlt (pLit "<") pNum (pLit ">") (pZeroOrMore pVar) (pLit "->") pExpr) (pLit ";")

mkAlt :: String -> Int -> String -> [Name] -> String -> CoreExpr -> CoreAlt
mkAlt _ tag _ vars _ expr = (tag, vars, expr)

pBinOp :: Parser String
pBinOp = let lits = map pLit binOps
         in  foldl pAlt (head lits) (tail lits)

pDefns :: Parser [(Name, CoreExpr)]
pDefns = pOneOrMoreWithSep pDefn (pLit ";") `pAlt` (pEmpty [])

pDefn :: Parser (Name, CoreExpr)
pDefn = pThen3 (\a b c -> (a,c)) pVar (pLit "=") pExpr

mkLet :: String -> [(String, Expr String)] -> String -> CoreExpr -> CoreExpr
mkLet rec defns _ expr = ELet (isRec rec) defns expr
   where isRec s = if s == "let" then nonRecursive else recursive

mkInFixApExpr :: CoreExpr -> String -> CoreExpr -> CoreExpr
mkInFixApExpr expr1 op expr2 = EAp (EAp (EVar op) expr1) expr2

pAExpr :: Parser CoreExpr
pAExpr = pApply pVar EVar `pAlt`
         pApply pNum ENum `pAlt`
         pThen5 mkConstr (pLit "Pack{") pNum (pLit ",") pNum (pLit "}")`pAlt`
         pThen3 mkParenExpr (pLit "(") pExpr (pLit ")")

mkConstr :: String -> Int -> String -> Int -> String -> CoreExpr 
mkConstr _ n1 _ n2 _ = EConstr n1 n2

mkParenExpr :: String -> CoreExpr -> String -> CoreExpr
mkParenExpr _ expr _ = expr

parse :: String -> CoreProgram
parse = syntax . map snd  . clex
