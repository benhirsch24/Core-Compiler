module Parser where
import Language
import Data.Char (isSpace, isDigit, isAlpha)

type Token = String
type Parser a = [Token] -> [(a, [Token])]

clex :: String -> [(Token, Int)]
clex cs = clex' 1 cs

clex' :: Int -> String -> [(Token, Int)]
clex' n (c:cs)
   | c == '\n' = clex' n+1 cs
   | isSpace c = clex' n cs
   | isDigit c = let num_token = c : takeWhile isDigit cs
                     rest_cs   = dropWhile isDigit cs
                 in  (num_token c, n) : clex' n rest_cs
   | isAlpha c = let var_tok = c : takeWhile isIdChar cs
                     rest_cs = dropWhile isIdChar cs
                 in  (var_tok, n) : clex' n rest_cs
   | c == '|' = if cs !! 0 == '|' then clex' n $ dropWhile (\c -> not $ c == '\n') cs else clex' n cs
   | otherwise = [c] : clex cs

twoCharOps :: [String]
twoCharOps = ["==", "-=", ">=", "<=", "->"]

isIdChar :: Char -> Bool
isIdChar c = isAlpha c || isDigit c || (c == '_')

syntax :: [Token] -> CoreProgram

pLit :: String -> Parser String
pLit _ [] = []
pLit s (tok:toks) 
   | s == tok | [(s, toks)]
   | otherwise = []

pVar :: Parser String
pVar [] = []

pAlt :: Parser a -> Parser a -> Parser a
pAlt p1 p2 toks = (p1 toks) ++ (p2 toks)

pThen :: (a -> b -> c) -> Parser a -> Parser b -> Parser c
pThen combine p1 p2 toks = 
   [ (combine v1 v2, toks2) | (v1, toks1) <- p1 toks, 
                              (v2, toks2) <- p2 toks1 ]

pZeroOrMore :: Parser a -> Parser [a]
pZeroOrMore p = (pOneOrMore p) `pAlt` (pEmpty [])

pEmpty :: a -> Parser a
pEmpty v toks = [(v, toks)]

pOneOrMore :: Parser a -> Parser [a]
pOneOrMore p (tok:toks) = 

parse :: String -> CoreProgram
parse = syntax . clex
