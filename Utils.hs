module Utils where
import Data.List (delete)

hInitial :: Heap a
hInitial = (0, [1..], [])

hAlloc :: Heap a -> a -> (Heap a, Addr)
hAlloc (size, (next:free), cts) n = (((size+1), free, (next, n):cts), next)

hUpdate :: Heap a -> Addr -> a -> Heap a
hUpdate (size, free, cts) a n = ( size, free, (a,n) : remove cts a )

hFree :: Heap a -> Addr -> Heap a
hFree (size, free, cts) a = (size-1, a:free, remove cts a)

hLookup :: Heap a -> Addr -> a
hLookup (size, free, cts) a =
   aLookup cts a (error ("can't find node " ++ showAddr a ++ " in heap"))

hAddresses :: Heap a -> [Addr]
hAddresses (_, _, cts) = [addr | (addr, node) <- cts]

hSize :: Heap a -> Int
hSize (size, _, _) = size

hNull :: Addr
hNull = 0

hIsNull :: Addr -> Bool
hIsNull a = a == 0

remove :: [(Int, a)] -> Int -> [(Int, a)]
remove [] a = error ("Attempt to update or free nonexistant address #" ++ shownum a)
remove ((a',n):cts) a
   | a == a' = cts
   | a /= a' = (a', n) : remove cts a

-- size, available, allocated
type Heap a = (Int, [Int], [(Int, a)])
type Addr   = Int

shownum :: Int -> String
shownum n = show n

showAddr :: Addr -> String
showAddr a = "#" ++ shownum a

type ASSOC a b = [(a,b)]

-- ASSOC a b -> a -> continuation -> b
aLookup [] k' def = def
aLookup ((k,v):rest) k' def
   | k == k' = v
   | k /= k' = aLookup rest k' def

aDomain :: ASSOC a b -> [a]
aDomain alist = [key | (key, _) <- alist]

aRange :: ASSOC a b -> [b]
aRange alist = [val | (key, val) <- alist]

aEmpty = []

getName :: NameSupply -> [Char] -> (NameSupply, [Char])
getName name_supply prefix = (name_supply + 1, makeName prefix name_supply)

getNames :: NameSupply -> [[Char]] -> (NameSupply, [[Char]])
getNames name_supply prefixes = (name_supply + length prefixes, zipWith makeName prefixes [name_supply..])

makeName :: [Char] -> Int -> [Char]
makeName prefix ns = prefix ++ "_" ++ shownum ns

initialNameSupply :: NameSupply
initialNameSupply = 0

type NameSupply = Int

space :: Int -> String
space n = take n $ repeat ' '
