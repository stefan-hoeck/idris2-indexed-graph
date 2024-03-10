module Main

import Data.Bits
import Data.Graph as G
import Data.DPair
import Data.Graph.Indexed as I
import Data.Graph.Indexed.Query.Visited
import Data.Graph.Indexed.Cycles
import Data.Graph.Indexed.Cycles2
import Data.Graph.Indexed.Cycles3
import Profile

%default total

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

gen : Nat -> (Nat -> a) -> List a
gen 0     f = [f 0]
gen (S k) f = f (S k) :: gen k f

genMay : Nat -> (Nat -> Maybe a) -> List a
genMay 0     f = toList (f 0)
genMay (S k) f = maybe (genMay k f) (:: genMay k f) (f k)

--------------------------------------------------------------------------------
--          Indexed Graph Generation
--------------------------------------------------------------------------------

0 ArrGr : (e,n : Type) -> Type
ArrGr = Data.Graph.Indexed.Types.Graph

record GraphData where
  constructor GD
  nodes : List Nat
  edges : List (Edge (length nodes) ())

tryEdge : (k,n : Nat) -> Maybe (Edge k ())
tryEdge k 0 = Nothing
tryEdge k (S n) = do
  f1 <- tryNatToFin {k} (S n)
  f2 <- tryNatToFin {k} (n)
  mkEdge f2 f1 ()

genEs : (n, k : Nat) -> List (Edge k ())
genEs n k = genMay n $ tryEdge k

graphData : Nat -> GraphData
graphData n =
  let ns := gen n id
      es := genEs n (length ns)
   in GD ns es

arrGraph : GraphData -> ArrGr () Nat
arrGraph (GD ns es) = G _ $ mkGraphL ns es

arrGraphN : Nat -> ArrGr () Nat
arrGraphN = arrGraph . graphData

labM : Nat -> ArrGr () Nat -> Maybe Nat
labM n (G k g) = case tryNatToFin {k} n of
  Just x => Just $ lab g x
  Nothing => Nothing

insM : Nat -> ArrGr () Nat -> ArrGr () Nat
insM n (G k g) = G _ $ insNodes g [n]

--------------------------------------------------------------------------------
--          Regular Graph Generation
--------------------------------------------------------------------------------

0 Gr : (e,n : Type) -> Type
Gr = Data.Graph.Types.Graph

pairs : Nat -> (List $ LNode Nat, List $ LEdge ())
pairs n =
  ( gen n $ \n => MkLNode (cast n) n
  , genMay n $ \x =>
      if x > 0 then (`MkLEdge` ()) <$> mkEdge (cast x) (cast x - 1) else Nothing)

graph : (List $ LNode Nat, List $ LEdge ()) -> Gr () Nat
graph (ns,es) = mkGraph ns es

graphN : Nat -> Gr () Nat
graphN = graph . pairs

--------------------------------------------------------------------------------
--          Visited
--------------------------------------------------------------------------------

testMVisited : {k : _} -> List (Fin k) -> Bool
testMVisited xs = visiting k (go xs)
  where
    go : List (Fin k) -> MVisited k -@ Ur Bool
    go []        v = done True v
    go (x :: xs) v =
      let False # v2 := mvisited x v | True # v2 => go xs v2
          v3         := mvisit x v2
       in go xs v3

testVisited : {k : _} -> List (Fin k) -> Bool
testVisited xs = go xs ini
  where
    go : List (Fin k) -> Visited k -> Bool
    go []        v = True
    go (x :: xs) v =
      if visited x v then go xs v else go xs (visit x v)

--------------------------------------------------------------------------------
--          Ring Generation
--------------------------------------------------------------------------------

getEdges : {k : _} -> List (Fin k) -> List (Maybe (Edge k ()))
getEdges []             = []
getEdges (FZ :: xs)     = mkEdge FZ last () :: getEdges xs
getEdges ((FS x) :: xs) = mkEdge (weaken x) (FS x) () :: getEdges xs

-- generate a single ring of size `n`
ringN : (n : Nat) -> ArrGr () ()
ringN n =
  let fins := allFinsFast n
      es   := getEdges fins
   in G n $ mkGraph (replicate _ () ) (mapMaybe id es)

searchRings : ArrGr () () -> Exists (List . Ring)
searchRings (G _ g) = Evidence _ $ searchAll g

covering
searchRingsSM : ArrGr () () -> Exists (List . Ring)
searchRingsSM (G _ g) = Evidence _ $ searchAllSM g

covering
searchRingsAM : ArrGr () () -> Exists (List . Ring)
searchRingsAM (G _ g) = Evidence _ $ searchAllMA g
--------------------------------------------------------------------------------
--          Benchmarks
--------------------------------------------------------------------------------

covering
bench : Benchmark Void
bench = Group "graph_ops"
  [ Group "Visited"
      [ Single "1"     (basic testVisited $ allFinsFast 1)
      , Single "32"    (basic testVisited $ allFinsFast 32)
      , Single "64"    (basic testVisited $ allFinsFast 64)
      , Single "128"   (basic testVisited $ allFinsFast 128)
      , Single "1024"  (basic testVisited $ allFinsFast 1024)
      , Single "65536" (basic testVisited $ allFinsFast 65536)
      ]
  , Group "MVisited"
      [ Single "1"     (basic testMVisited $ allFinsFast 1)
      , Single "32"    (basic testMVisited $ allFinsFast 32)
      , Single "64"    (basic testMVisited $ allFinsFast 64)
      , Single "128"   (basic testMVisited $ allFinsFast 128)
      , Single "1024"  (basic testMVisited $ allFinsFast 1024)
      , Single "65536" (basic testMVisited $ allFinsFast 65536)
      ]
  , Group "mkGraph map-based"
      [ Single "1"     (basic graph $ pairs 1)
      , Single "10"    (basic graph $ pairs 10)
      , Single "100"   (basic graph $ pairs 100)
      , Single "1000"  (basic graph $ pairs 1000)
      , Single "10000" (basic graph $ pairs 10000)
      ]
  , Group "mkGraph array-based"
      [ Single "1"     (basic arrGraph $ graphData 1)
      , Single "10"    (basic arrGraph $ graphData 10)
      , Single "100"   (basic arrGraph $ graphData 100)
      , Single "1000"  (basic arrGraph $ graphData 1000)
      , Single "10000" (basic arrGraph $ graphData 10000)
      ]
  , Group "lab map-based"
      [ Single "1"     (basic (`lab` 0)    $ graphN 1)
      , Single "10"    (basic (`lab` 5)    $ graphN 10)
      , Single "100"   (basic (`lab` 50)   $ graphN 100)
      , Single "1000"  (basic (`lab` 500)  $ graphN 1000)
      , Single "10000" (basic (`lab` 5000) $ graphN 10000)
      ]
  , Group "lab array-based"
      [ Single "1"     (basic (labM 0)    $ arrGraphN 1)
      , Single "10"    (basic (labM 5)    $ arrGraphN 10)
      , Single "100"   (basic (labM 50)   $ arrGraphN 100)
      , Single "1000"  (basic (labM 500)  $ arrGraphN 1000)
      , Single "10000" (basic (labM 5000) $ arrGraphN 10000)
      ]
  , Group "insert map-based"
      [ Single "1"     (basic (insNode 1 1)     $ graphN 1)
      , Single "10"    (basic (insNode 11 1)    $ graphN 10)
      , Single "100"   (basic (insNode 111 1)   $ graphN 100)
      , Single "1000"  (basic (insNode 1111 1)  $ graphN 1000)
      , Single "10000" (basic (insNode 11111 1) $ graphN 10000)
      ]
  , Group "insert array-based"
      [ Single "1"     (basic (insM 1) $ arrGraphN 1)
      , Single "10"    (basic (insM 1) $ arrGraphN 10)
      , Single "100"   (basic (insM 1) $ arrGraphN 100)
      , Single "1000"  (basic (insM 1) $ arrGraphN 1000)
      , Single "10000" (basic (insM 1) $ arrGraphN 10000)
      ]
  , Group "searchRings" [
       Single "1"     (basic searchRings $ ringN 1)
      , Single "10"     (basic searchRings $ ringN 10)
      , Single "100"     (basic searchRings $ ringN 100)
      , Single "1000"     (basic searchRings $ ringN 1000)
      , Single "10000"     (basic searchRings $ ringN 10000)
      ]
  , Group "searchRingsSM" [
        Single "1"     (basic searchRingsSM $ ringN 1)
      , Single "10"     (basic searchRingsSM $ ringN 10)
      , Single "100"     (basic searchRingsSM $ ringN 100)
      , Single "1000"     (basic searchRingsSM $ ringN 1000)
      , Single "10000"     (basic searchRingsSM $ ringN 10000)
      ]
  , Group "searchRingsAM" [
        Single "1"     (basic searchRingsAM $ ringN 1)
      , Single "10"     (basic searchRingsAM $ ringN 10)
      , Single "100"     (basic searchRingsAM $ ringN 100)
      , Single "1000"     (basic searchRingsAM $ ringN 1000)
      , Single "10000"     (basic searchRingsAM $ ringN 10000)
      ]
  ]

covering
main : IO ()
main = runDefault (const True) Table show bench
