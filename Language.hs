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
       ("S", ["f", "g", "x"], EAp (EAp (EVar "f") (EVar "a")) 
                                  (EAp (EVar "g") (EVar "x"))),
       ("compose", ["f", "g", "x"], EAp (EVar "f") 
                                        (EAp (EVar "g") (EVar "x"))),
       ("twice", ["f"], EAp (EAp (EVar "compose") (EVar "f")) (EVar "f")) ]



