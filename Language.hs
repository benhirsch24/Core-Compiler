module Language where
import Iseq

data Expr a
   = EVar Name
   | ENum Int
   | EConstr Int Int -- Constructor
   | EAp (Expr a) (Expr a)
   | ELet IsRec [(a, Expr a)] (Expr a) -- bool, defs, body
   | ECase (Expr a) [Alter a] -- cond, alternatives
   | ELam [a] (Expr a) -- lambda abstractions
   deriving (Show)

type CoreExpr = Expr Name
type Name = String
type IsRec = Bool
type Alter a = (Int, [a], Expr a)
type CoreAlt = Alter Name
type Program a = [ScDefn a]
type CoreProgram = Program Name
type ScDefn a = (Name, [a], Expr a)
type CoreScDefn = ScDefn Name

recursive, nonRecursive :: IsRec
recursive = True
nonRecursive = False

data PartialExpr = NoOp | FoundOp Name CoreExpr

bindersOf :: [(a,b)] -> [a]
bindersOf defns = [name | (name, rhs) <- defns]

rhssOf :: [(a,b)] -> [b]
rhssOf defns = [rhs | (name, rhs) <- defns]

isAtomicExpr :: Expr a -> Bool
isAtomicExpr (EVar v) = True
isAtomicExpr (ENum n) = True
isAtomicExpr _ = False

preludeDefs :: CoreProgram
preludeDefs
   = [ ("I", ["x"], EVar "x"),
       ("K", ["x", "y"], EVar "x"),
       ("K1", ["x", "y"], EVar "y"),
       ("S", ["f", "g", "x"], EAp (EAp (EVar "f") (EVar "x")) 
                                  (EAp (EVar "g") (EVar "x"))),
       ("compose", ["f", "g", "x"], EAp (EVar "f") 
                                        (EAp (EVar "g") (EVar "x"))),
       ("twice", ["f"], EAp (EAp (EVar "compose") (EVar "f")) (EVar "f"))
       ]

extraPreludeDefs
   = [ ("True", ["t", "f"], EVar "t"),
       ("False", ["t", "f"], EVar "f"),
       ("if", [], EVar "I"),
       ("and", ["b1", "b2", "t", "f"], EAp (EAp (EVar "b1") (EAp (EAp (EVar "b2") (EVar "t")) (EVar "f"))) (EVar "f")), 
       ("or", ["b1", "b2", "t", "f"], EAp (EAp (EVar "b1") (EVar "t")) (EAp (EAp (EVar "b2") (EVar "t")) (EVar "f"))),
       ("not", ["b", "t", "f"], EAp (EAp (EVar "b") (EVar "f")) (EVar "t")),
       ("xor", ["x", "y"], EAp (EAp (EVar "or") (EAp (EAp (EVar "and") (EAp (EVar "not") (EVar "x"))) (EVar "y"))) (EAp (EAp (EVar "and") (EAp (EVar "not") (EVar "y"))) (EVar "x"))),
       ("pair", ["a", "b", "f"], EAp (EAp (EVar "f") (EVar "a")) (EVar "b")),
       ("casePair", [], EVar "I"),
       ("fst", ["p"], EAp (EVar "p") (EVar "K")),
       ("snd", ["p"], EAp (EVar "p") (EVar "K1")),
       ("nil", ["cn", "cc"], EVar "cn"),
       ("cons", ["a", "b", "cn", "cc"], EAp (EAp (EVar "cc") (EVar "a")) (EVar "b")),
       ("caseList", [], EVar "I"),
       ("head", ["xs"], EAp (EAp (EAp (EVar "caseList") (EVar "xs")) (EVar "abort")) (EVar "K")),
       ("tail", ["xs"], EAp (EAp (EAp (EVar "caseList") (EVar "xs")) (EVar "abort")) (EVar "K1")),
       ("length", ["xs"], EAp (EAp (EAp (EVar "caseList")  (EVar "xs")) (ENum 0)) (EVar "length'")),
       ("length'", ["x", "xs"], EAp (EVar "+") (EAp (EVar "length") (EVar "xs"))),
       ("printList", ["xs"], EAp (EAp (EAp (EVar "caseList") (EVar "xs")) (EVar "stop")) (EVar "printCons")),
       ("printCons", ["h", "t"], EAp (EAp (EVar "print") (EVar "h")) (EAp (EVar "printList") (EVar "t")))
        ]
