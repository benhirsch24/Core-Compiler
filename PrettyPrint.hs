module PrettyPrinter where
import Language
import Iseq

pprint :: CoreProgram -> String
pprint prog = iDisplay (pprProgram prog)

pprProgram :: CoreProgram -> Iseq
pprProgram defns = iInterleave iNewline (map pprScDefn defns)

pprScDefn :: CoreScDefn -> Iseq
pprScDefn (name, vars, expr) = iStr name `iAppend` iStr " " `iAppend` iInterleave (iStr " ") (map iStr vars) `iAppend` iStr "= " `iAppend` pprExpr expr

pprExpr :: CoreExpr -> Iseq
pprExpr (EVar v) = iStr v
pprExpr (EAp e1 e2) = (pprExpr e1) `iAppend` (iStr " ") `iAppend` pprAExpr e2
pprExpr (ECase expr as) = 
   iStr "case " `iAppend` pprExpr expr `iAppend` iStr " of " `iAppend` iIndent (pprCases as)
pprExpr (ELam vars expr) = iStr "\\ " `iAppend` iInterleave (iStr " ") (map iStr vars) `iAppend` iStr " . " `iAppend` pprExpr expr
pprExpr (ELet isrec defns expr) =
   iConcat [ iStr keyword, iNewline, iStr " ", 
             iIndent (pprDefns defns), iNewline,
             iStr "in ", pprExpr expr]
   where keyword = if isrec then "letrec" else "let"

pprCases :: [Alter Name] -> Iseq
pprCases as = iInterleave sep (map pprCase as)
   where sep = iConcat [ iStr " ;", iNewline ]

pprCase :: Alter Name -> Iseq
pprCase (tag, as, expr) = tagSeq `iAppend` iInterleave (iStr " ") (map iStr as) `iAppend` pprExpr expr
   where tagSeq = iStr "<" `iAppend` iStr (show tag) `iAppend` iStr ">"

pprDefns :: [(Name, CoreExpr)] -> Iseq
pprDefns defns = iInterleave sep (map pprDefn defns)
   where sep = iConcat [ iStr ";", iNewline ]

pprDefn :: (Name, CoreExpr) -> Iseq
pprDefn (name, expr) = iConcat [ iStr name, iStr " = ", iIndent (pprExpr expr) ]

pprAExpr :: CoreExpr -> Iseq
pprAExpr e 
   | isAtomicExpr e = pprExpr e
   | otherwise = iStr "(" `iAppend` pprExpr e `iAppend` iStr ")"

mkMultiAp :: Int -> CoreExpr -> CoreExpr -> CoreExpr
mkMultiAp n e1 e2 = foldl EAp e1 (take n e2s)
                    where e2s = e2 : e2s
