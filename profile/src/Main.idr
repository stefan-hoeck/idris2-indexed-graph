module Main

import Data.Graph as G
import Data.DPair
import Data.Graph.Indexed as I
import Data.Graph.Indexed.Cycles
import Data.Graph.Indexed.Cycles2
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

covering
searchRings : ArrGr () () -> Exists (List . Ring)
searchRings (G _ g) = Evidence _ $ searchAll g

covering
searchRingsSM : ArrGr () () -> Exists (List . Ring)
searchRingsSM (G _ g) = Evidence _ $ searchAllSM g
--------------------------------------------------------------------------------
--          Benchmarks
--------------------------------------------------------------------------------

covering
bench : Benchmark Void
bench = Group "graph_ops" [
---    Group "mkGraph" [
---        Single "G 1"     (basic graph $ pairs 1)
---      , Single "A 1"     (basic arrGraph $ graphData 1)
---      , Single "G 10"    (basic graph $ pairs 10)
---      , Single "A 10"    (basic arrGraph $ graphData 10)
---      , Single "G 100"   (basic graph $ pairs 100)
---      , Single "A 100"   (basic arrGraph $ graphData 100)
---      , Single "G 1000"  (basic graph $ pairs 1000)
---      , Single "A 1000"  (basic arrGraph $ graphData 1000)
---      , Single "G 10000" (basic graph $ pairs 10000)
---      , Single "A 10000" (basic arrGraph $ graphData 10000)
---      ]
---  , Group "lab" [
---        Single "G 1"     (basic (`lab` 0) $ graphN 1)
---      , Single "A 1"     (basic (labM 0) $ arrGraphN 1)
---      , Single "G 10"    (basic (`lab` 5) $ graphN 10)
---      , Single "A 10"    (basic (labM 5) $ arrGraphN 10)
---      , Single "G 100"   (basic (`lab` 50) $ graphN 100)
---      , Single "A 100"   (basic (labM 50) $ arrGraphN 100)
---      , Single "G 1000"  (basic (`lab` 500) $ graphN 1000)
---      , Single "A 1000"  (basic (labM 500) $ arrGraphN 1000)
---      , Single "G 10000" (basic (`lab` 5000) $ graphN 10000)
---      , Single "A 10000" (basic (labM 5000) $ arrGraphN 10000)
---      ]
    Group "searchRings" [
        Single "1"     (basic searchRings $ ringN 1)
      , Single "10"     (basic searchRings $ ringN 10)
      , Single "100"     (basic searchRings $ ringN 100)
      , Single "1000"     (basic searchRings $ ringN 1000)
      , Single "10000"     (basic searchRings $ ringN 1000)
      ]
  , Group "searchRingsSM" [
        Single "1"     (basic searchRingsSM $ ringN 1)
      , Single "10"     (basic searchRingsSM $ ringN 10)
      , Single "100"     (basic searchRingsSM $ ringN 100)
      , Single "1000"     (basic searchRingsSM $ ringN 1000)
      , Single "10000"     (basic searchRingsSM $ ringN 1000)
      ]
  ]
--   , Group "insert" [
--         Single "1"     (basic (insert 333 "") $ full 1)
--       , Single "10"    (basic (insert 333 "") $ full 10)
--       , Single "100"   (basic (insert 333 "") $ full 100)
--       , Single "1000"  (basic (insert 333 "") $ full 1000)
--       , Single "10000" (basic (insert 333 "") $ full 10000)
--       ]
--   , Group "delete" [
--         Single "1"     (basic (delete 333) $ full 1)
--       , Single "10"    (basic (delete 333) $ full 10)
--       , Single "100"   (basic (delete 333) $ full 100)
--       , Single "1000"  (basic (delete 333) $ full 1000)
--       , Single "10000" (basic (delete 333) $ full 10000)
--       ]
--   ]

covering
main : IO ()
main = runDefault (const True) Table show bench
