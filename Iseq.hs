module Iseq where

data Iseq = INil
   | IStr String
   | IAppend Iseq Iseq
   | IIndent Iseq
   | INewline
   deriving (Show)

flatten :: Int -> [(Iseq,Int)] -> String
flatten _ [] = ""
flatten col ((INewline, indent) : seqs) = '\n' : (space indent) ++ (flatten indent seqs)
   where space i = take i (repeat ' ')
flatten col ((IIndent seq, indent) : seqs) = flatten col ((seq, col):seqs)
flatten col ((IAppend seq1 seq2, indent) : seqs) = flatten col ((seq1, col) : (seq2, col) : seqs)
flatten col ((IStr str, indent) : seqs) = str ++ (flatten col seqs)
flatten col ((INil, indent) : seqs) = flatten col seqs

iNil :: Iseq -- empty iseq
iNil = INil

iStr :: String -> Iseq
iStr str = IStr str

iNum :: Int -> Iseq
iNum n = iStr (show n)

iFWNum :: Int -> Int -> Iseq
iFWNum width n
   = iStr (space (width - length digits) ++ digits)
   where digits = show n
         space i = take i $ repeat ' '

iLayn :: [Iseq] -> Iseq
iLayn seqs = iConcat (map lay_item (zip [1..] seqs))
   where lay_item (n, seq) = iConcat [ iFWNum 4 n, iStr ") ", iIndent seq, iNewline ]

iAppend :: Iseq -> Iseq -> Iseq
iAppend seq1 seq2 = IAppend seq1 seq2

iNewline :: Iseq
iNewline = INewline

iIndent :: Iseq -> Iseq
iIndent seq = IIndent seq

iConcat :: [Iseq] -> Iseq
iConcat [] = INil
iConcat (seq:rest) = seq `iAppend` iConcat rest

iInterleave :: Iseq -> [Iseq] -> Iseq
iInterleave _ [] = iNil
iInterleave sep (seq:rest) = seq `iAppend` sep `iAppend` (iInterleave sep rest)

iDisplay :: Iseq -> String
iDisplay seq = flatten 0 [(seq, 0)]
