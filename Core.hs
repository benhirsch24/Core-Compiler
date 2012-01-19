import Utils
import Language
import Data.List (mapAccumL)
import Parser
import PrettyPrint
import Iseq
import System.IO
import qualified System.Environment as SysEnv

main :: IO ()
main = do 
   file <- SysEnv.getArgs
   withFile (head file) ReadMode (\handle -> do
            contents <- hGetContents handle
            putStr $ runProg contents)

runProg :: [Char] -> [Char]
runProg = showResults . eval . compile . parse

type TiStack = [Addr]
type TiDump = [TiStack]
type TiHeap = Heap Node
type TiGlobals = ASSOC Name Addr
type TiStats = Int
type TiState = (TiStack, TiDump, TiHeap, TiGlobals, TiStats)


data Node = NAp Addr Addr
          | NSupercomb Name [Name] CoreExpr
          | NNum Int
          | NInd Addr
          | NPrim Name Primitive
          | NData Int [Addr]

data Primitive = Neg
               | Add
               | Sub
               | Mul
               | Div
               | PrimConstr {t :: Int, a :: Int}
               | If
               | Greater
               | GreaterEq
               | Less
               | LessEq
               | Eq
               | NotEq
               | CasePair
               | CaseList
               | Abort
               | Stop
               deriving (Show)

primitives :: ASSOC Name Primitive
primitives = [ ("negate", Neg),
               ("+",      Add), ("-", Sub),
               ("*",      Mul), ("/", Div),
               ("if",     If),  (">", Greater),
               (">=",     GreaterEq),
               ("<",      Less), ("<=", LessEq),
               ("==",     Eq),  ("!=", NotEq),
               ("casePair", CasePair), ("caseList", CaseList),
               ("abort", Abort)
             ]

compile :: CoreProgram -> TiState
compile program
   = let address_of_main = aLookup globals "main" (error "main is not defined")
         initial_stack  = [address_of_main]
         (initial_heap, globals) = buildInitialHeap sc_defs
         sc_defs = program ++ preludeDefs ++ extraPreludeDefs
     in  (initial_stack, initialTiDump, initial_heap, globals, tiStatInitial)


buildInitialHeap :: [CoreScDefn] -> (TiHeap, TiGlobals)
buildInitialHeap sc_defs
   = let (heap1, sc_addrs) = mapAccumL allocateSc hInitial sc_defs
         (heap2, prim_addrs) = mapAccumL allocatePrim heap1 primitives
     in  (heap2, sc_addrs ++ prim_addrs)

allocateSc :: TiHeap -> CoreScDefn -> (TiHeap, (Name, Addr))
allocateSc heap (name, args, body) =
   let (heap', addr) = hAlloc heap (NSupercomb name args body)
   in  (heap', (name, addr))

allocatePrim :: TiHeap -> (Name, Primitive) -> (TiHeap, (Name, Addr))
allocatePrim heap (name, prim)
   = let (heap', addr) = hAlloc heap (NPrim name prim)
     in  (heap', (name, addr))

eval :: TiState -> [TiState]
eval state = let rest_states = if tiFinal state 
                              then []
                              else eval $ doAdmin (step state) 
             in  state : rest_states

doAdmin :: TiState -> TiState
doAdmin state = applyToStats tiStatIncSteps state

step :: TiState -> TiState
step state@(stack, dump, heap, globals, stats)
   = dispatch $ hLookup heap (head stack)
   where
   dispatch (NNum n)                  = numStep  state n
   dispatch (NAp a1 a2)               = apStep   state a1 a2
   dispatch (NSupercomb sc args body) = scStep   state sc args body
   dispatch (NInd addr)               = indStep  state addr
   dispatch (NPrim name prim)         = primStep state prim
   dispatch (NData tag addrs)         = dataStep state tag addrs

dataStep :: TiState -> Int -> [Addr] -> TiState
dataStep ((a:[]), dump, heap, globals, stats) tag addrs = (head dump, tail dump, heap, globals, stats)
dataStep _ _ _ = error "Shouldn't have gotten here"

primStep :: TiState -> Primitive -> TiState
-- primStep for Negate
primStep (a:a1:[], dump, heap, globals, stats) Neg
   = let (NAp _ b) =  hLookup heap a1
     in  case hLookup heap b of
            NNum n      -> (a1:[], dump, hUpdate heap a1 $ NNum (-n), globals, stats)
            otherwise   -> (b:[], (a1:[]):dump, heap, globals, stats)
-- primSteps for + - * /
primStep state Add = primArith state (+)
primStep state Sub = primArith state (-)
primStep state Mul = primArith state (*)
primStep state Div = primArith state (div)

-- primSteps for comparison operators
primStep state Greater = primComp state (>)
primStep state GreaterEq = primComp state (>=)
primStep state Less = primComp state (<)
primStep state LessEq = primComp state (<=)
primStep state Eq = primComp state (==)
primStep state NotEq = primComp state (/=)

-- primStep Abort!
primStep state Abort = error "Aborted"

-- primStep for casePair
-- Primitive casePair
-- NAp ^ Pair
-- NAp ^ Function
primStep state@(stack@(a:a1:a2:[]), dump, heap, globals, stats) CasePair =
   let arg_addrs@(addr1:addr2:[]) = getArgs heap stack
       (n1:n2:[]) = map (hLookup heap) arg_addrs
   in  case n1 of
         NData tag (data_addr1:data_addr2:[]) -> 
            case n2 of
               NSupercomb name args body ->
                  let (heap', addr) = hAlloc heap $ NAp addr2 data_addr1
                      heap'' = hUpdate heap' a2 $ NAp addr data_addr2
                  in  (addr2:addr:a2:[], dump, heap'', globals, stats)
               NAp nap1 nap2 -> (addr2:[], stack:dump, heap, globals, stats)
               otherwise -> error "casePair f not a supercomb or ap"
         NAp na1 na2 -> (addr1:[], stack:dump, heap, globals, stats)
         NSupercomb _ _ _  -> (addr1:[], stack:dump, heap, globals, stats)
         otherwise -> error "casePair not a ndata or nap or sc"
   
   
-- primStep caseList
-- Primitive caseList
-- NAp ^ Cons
-- NAp ^ cn
-- NAp ^ cc
primStep state@(stack@(a:a1:a2:a3:[]), dump, heap, globals, stats) CaseList =
   case li of
      NData tag (hd:tl:[]) ->
         case tag of
            1 -> (a3:[], dump, hUpdate heap a3 $ NInd cn, globals, stats)
            2 -> let (heap', addr) = hAlloc heap $ NAp cc hd
                     heap'' = hUpdate heap' a3 $ NAp addr tl 
                 in  (cc:addr:a3:[], dump, heap'', globals, stats)
      NAp _ _ -> (liaddr:[], stack:dump, heap, globals, stats)
      NSupercomb _ _ _ -> (liaddr:[], stack:dump, heap, globals, stats)
      otherwise -> error "caselist list is not ndata nap or nsupercomb"
   where
   arg_addrs@(liaddr:cn:cc:[]) = getArgs heap stack
   (li:_:_:[]) = map (hLookup heap) arg_addrs

--primStep for Constrs
primStep (stack, dump, heap, globals, stats) (PrimConstr tag arity) =
   let arg_addrs = getArgs heap stack
       an        = last stack -- root of the redex
       data_node = NData tag arg_addrs 
   in  (an:[], dump, hUpdate heap an data_node, globals, stats)

--primStep for IF
primStep (stack@(a:a1:a2:a3:[]), dump, heap, globals, stats) If =
   case hLookup heap condition of -- second object on stack should be condition
      NData tag addrs -> let exp = if tag == 1 
                                   then exp2
                                   else exp1 
                             heap' = hUpdate heap a3 $ NInd exp
                         in  (a3:[], dump, heap', globals, stats)
      NAp _ _ -> (condition:[], stack:dump, heap, globals, stats)
      NSupercomb _ _ _ -> (condition:[], stack:dump, heap, globals, stats)
      otherwise -> error "primStep IF, condition not ndata nap or nsupercomb"
   where
   (condition:exp1:exp2:[]) = getArgs heap stack

-- primDyadic because there's arithmetic and boolean operators
-- so arithmetic functions return an NNum,
-- comparison functions return an NData (True/False)
primDyadic :: TiState -> (Node -> Node -> Node) -> TiState
primDyadic (stack@(a:a1:a2:[]), dump, heap, globals, stats) fun =
   let (n1:n2:[]) = map (hLookup heap) $ getArgs heap stack
       (addr1:addr2:[]) = getArgs heap stack
   in  case n1 of
         NNum na -> case n2 of
                  NNum nb -> (a2:[], dump, hUpdate heap a2 $ fun n1 n2, globals, stats)
                  NAp _ _ -> (addr2:[], stack:dump, heap, globals, stats)
                  otherwise -> error "error in primDyadic not nnum or nap2"
         NAp _ _ -> (addr1:[], stack:dump, heap, globals, stats)
         NSupercomb _ _ _ -> (addr1:[], stack:dump, heap, globals, stats)
         otherwise -> error "error in primDyadic not nnum or nap1"

-- comparison
primComp :: TiState -> (Int -> Int -> Bool) -> TiState
primComp state op =
   primDyadic state (compFun op) 
   where
   compFun op (NNum a) (NNum b) = let tag = if a `op` b
                                            then 2
                                            else 1
                                  in  NData tag []
   compFun op _ _ = error "That's not Jack"
       
-- arithmetic
primArith :: TiState -> (Int -> Int -> Int) -> TiState
primArith state op =
   primDyadic state (arithFun op)
   where
   arithFun op (NNum a) (NNum b) = (NNum (a `op` b))
   arithFun op _ _ = error "Wrong data nodes"

numStep :: TiState -> Int -> TiState
numStep (a:[], dump, heap, globals, stats) n
   = (head dump, tail dump, heap, globals, stats)
numStep (stack, dump, heap, globals, stats) n = error "Error in numStep"

apStep :: TiState -> Addr -> Addr -> TiState
apStep (stack, dump, heap, globals, stats) a1 a2
   = case hLookup heap a2 of
      (NInd a3) -> (stack, dump, hUpdate heap (head stack) $ NAp a1 a3, globals, stats)
      otherwise -> (a1:stack, dump, heap, globals, stats)

scStep :: TiState -> Name -> [Name] -> CoreExpr -> TiState
scStep (stack, dump, heap, globals, stats) sc_name arg_names body
   | length arg_names <= length stack
      = let new_stack = (drop (length arg_names) stack)
            new_heap = instantiateAndUpdate body (stack !! length arg_names) heap env
            env = arg_bindings ++ globals
            arg_bindings = zip arg_names (getArgs heap stack)
         in (new_stack, dump, new_heap, globals, stats)
   | otherwise         = error "Not applied to enough args"

indStep :: TiState -> Addr -> TiState
indStep ((a:stack), dump, heap, globals, stats) addr = (addr:stack, dump, hUpdate heap a (hLookup heap addr), globals, stats)

{- getArgs gets the arguments off the stack.
   So a stack looking like:
   Prim Add
   NAp _ 3
   NAp _ 4

   getArgs of that stack returns 3:4:[]
-}
getArgs :: TiHeap -> TiStack -> [Addr]
getArgs heap (sc:stack) = map getArg stack
   where getArg addr = arg
                        where (NAp fun arg) = hLookup heap addr

instantiate :: CoreExpr -> TiHeap -> ASSOC Name Addr -> (TiHeap, Addr)
instantiate (ENum n) heap env = hAlloc heap (NNum n)
instantiate (EAp e1 e2) heap env = hAlloc heap2 (NAp a1 a2)
   where 
   (heap1, a1) = instantiate e1 heap env
   (heap2, a2) = instantiate e2 heap1 env
instantiate (EVar v) heap env = (heap, aLookup env v (error ("Undefined name " ++ show v)))
instantiate (EConstr tag arity) heap env
   = hAlloc heap $ NPrim "Pack" (PrimConstr tag arity)
instantiate (ELet isrec defs body) heap env
   = instantiateLet isrec defs body heap env
instantiate (ECase e alts) heap env = error "Can't instantiate case exprs"
instantiateLet isrec defs body heap env 
   = if isrec then recursiveLet else nonrecursiveLet
   where
   oppInstantiate e h d = instantiate d h e
   augEnv ev pair = (pair:ev, ())
   nonrecursiveLet = let (heap', defAddrs) = mapAccumL (oppInstantiate env) heap $ rhssOf defs
                         (newenv,_)   = mapAccumL augEnv env $ zip (bindersOf defs) defAddrs
                     in  instantiate body heap' newenv
   recursiveLet = let (heap', defAddrs) = mapAccumL (oppInstantiate newenv) heap $ rhssOf defs
                      (newenv,_) = mapAccumL augEnv env $ zip (bindersOf defs) defAddrs
                  in  instantiate body heap' newenv

instantiateAndUpdate :: CoreExpr -> Addr -> TiHeap -> ASSOC Name Addr -> TiHeap
instantiateAndUpdate (EVar v) upd_addr heap env
   = hUpdate heap upd_addr $ NInd $ aLookup env v (error "Can't find var")
instantiateAndUpdate (ENum n) upd_addr heap env
   = hUpdate heap upd_addr (NNum n)
instantiateAndUpdate (EConstr tag arity) upd_addr heap env =
   hUpdate heap upd_addr $ NPrim "Pack" $ PrimConstr tag arity
instantiateAndUpdate (EAp e1 e2) upd_addr heap env
   = let (heap1, a1) = instantiate e1 heap env
         (heap2, a2) = instantiate e2 heap1 env
     in  hUpdate heap2 upd_addr (NAp a1 a2)
instantiateAndUpdate letExpr@(ELet isrec defs body) upd_addr heap env
   = let (heap', addr) = instantiate letExpr heap env
     in  hUpdate heap' upd_addr (NInd addr)
instantiateAndUpdate (ECase guard alts) upd_addr heap env
   = error "Can't do cases yet"
                            
initialTiDump :: TiDump
initialTiDump = []

tiStatInitial :: TiStats
tiStatInitial = 0

tiStatIncSteps :: TiStats -> TiStats
tiStatIncSteps s = s+1

tiStatGetSteps :: TiStats -> Int
tiStatGetSteps s = s

applyToStats :: (TiStats -> TiStats) -> TiState -> TiState
applyToStats stats_fun (stack, dump, heap, sc_defs, stats) =
   (stack, dump, heap, sc_defs, stats_fun stats)

tiFinal :: TiState -> Bool
tiFinal ([], _, _, _, _) = error "Empty Stack!"
tiFinal (addr:rest, dump, heap, globals, stats)
   | length rest == 0 && length dump == 0 =
      case hLookup heap addr of
         NPrim _ Stop -> True
         otherwise -> isDataNode $ hLookup heap addr
   | otherwise       = False

isDataNode :: Node -> Bool
isDataNode (NNum n) = True
isDataNode (NData _ _) = True
isDataNode _        = False


showResults :: [TiState] -> [Char]
showResults states = iDisplay (iConcat [ iLayn (map showState states),
                                         showStats (last states),
                                         iNewline
                                       ])

showState :: TiState -> Iseq
showState (stack, dump, heap, _, _)
   = iConcat [ showStack heap stack, showHeap heap stack, showDump heap stack dump, iNewline ]

showDump :: TiHeap -> TiStack -> TiDump -> Iseq
showDump heap stack dump
   = iConcat [ iNewline, iStr " Dump [",
               iIndent ( iInterleave iNewline (map show_dump_item $ dump)),
               iStr " ]"]
   where
   show_dump_item stk = showStack heap stk

showHeap :: TiHeap -> TiStack -> Iseq
showHeap heap stack
   = iConcat [ iNewline, iStr " Heap [",
               iIndent (iInterleave iNewline (map show_heap_item $ hAddresses heap)),
               iStr " ]" ]
   where
   show_heap_item addr
      = iConcat [ showFWAddr addr, iStr ": ",
                  showStkNode heap (hLookup heap addr)
                ]

showStack :: TiHeap -> TiStack -> Iseq
showStack heap stack
   = iConcat [ iStr "Stk [",
               iIndent (iInterleave iNewline (map show_stack_item stack)),
               iStr " ]"
             ]
   where
   show_stack_item addr
      = iConcat [ showFWAddr addr, iStr ": ",
                  showStkNode heap (hLookup heap addr)
                ]

showStkNode :: TiHeap -> Node -> Iseq
showStkNode heap (NAp fun_addr arg_addr)
   = iConcat [ iStr "NAp ", showFWAddr fun_addr,
               iStr " ", showFWAddr arg_addr, iStr " (",
               showNode (hLookup heap arg_addr), iStr ")"
             ]
showStkNode heap node = showNode node

showNode :: Node -> Iseq
showNode (NAp a1 a2) = iConcat [ iStr "NAp ", Main.showAddr a1,
                                 iStr " ",    Main.showAddr a2 ]
showNode (NSupercomb name args body) = iStr ("NSupercomb " ++ name)
showNode (NNum n) = (iStr "NNum ") `iAppend` (iNum n)
showNode (NInd addr) = iStr "NInd " `iAppend` Main.showAddr addr
showNode (NPrim name prim) = iStr ("Primitive: " ++ name ++ " " ++ show prim)
showNode (NData tag addrs)
   = iConcat [ iStr ("NData: " ++ show tag ++ " "),
               iInterleave (iStr " ") $ map Main.showAddr addrs ]
   

showAddr :: Addr -> Iseq
showAddr addr = iStr (show addr)

showFWAddr :: Addr -> Iseq -- show addrs in field of width 4
showFWAddr addr = let str = show addr
                  in  iStr (space (4 - length str) ++ str)

showStats :: TiState -> Iseq
showStats (stack, dump, heap, globals, stats)
   = iConcat [ iNewline, iNewline, iStr "Total number of steps = ",
               iNum (tiStatGetSteps stats) ]
