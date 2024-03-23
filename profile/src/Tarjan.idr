module Tarjan

import Data.List
import Data.Graph.Indexed
import Data.Graph.Indexed.Subgraph
import Profile

%default total

tryEdge : {k : _} -> (m,n : Nat) -> Maybe (Edge k ())
tryEdge m n = do
  f1 <- tryNatToFin m
  f2 <- tryNatToFin n
  mkEdge f2 f1 ()

toNext : {n : Nat} -> (x : Nat) -> Maybe (Edge n ())
toNext x = tryEdge x (S x)

-- a chain of `n` fused cyclohexane rings
chain : (n : Nat) -> Graph () ()
chain n =
  let tot := 4*n + 2
   in G tot $ mkGraph
        (replicate tot ())
        (catMaybes $ map toNext [0..tot] ++ map (close tot) [0..n])
  where
    close : (tot : Nat) -> Nat -> Maybe (Edge tot ())
    close tot x = tryEdge (2 * x) ((4*n+1) `minus` (2*x))

-- a sequence of `n` isolate cyclohexane rings
seq : (n : Nat) -> Graph () ()
seq n =
  let tot := 6 * n
   in G tot $ mkGraph
        (replicate _ ())
        (catMaybes $ ([0..n] >>= ring tot . (6*)) ++ map (link tot) [0..n])
  where
    ring : (tot : Nat) -> Nat -> List (Maybe $ Edge tot ())
    ring tot k = tryEdge k (k+5) :: map (\x => tryEdge (k+x) (k+x+1)) [0..4]

    link : (tot : Nat) -> Nat -> Maybe (Edge tot ())
    link tot k = tryEdge (k*6 + 3) (k*6 + 6)

-- a disconnected graph of 4n+2 isolate nodes
disc : (n : Nat) -> Graph () ()
disc n = G (4 * n + 2) $ mkGraph (replicate _ ()) []

countSG : Graph () () -> Nat
countSG (G o g) = order $ subgraphL g (nodes g)

countComps : Graph () () -> Nat
countComps (G o g) = length $ connectedComponents g

countBicomps : Graph () () -> Nat
countBicomps (G o g) = length $ biconnectedComponents g

bench : Benchmark Void
bench = Group "subgraphs"
  [ Group "subgraph_connected"
      [ Single "1"     (basic countSG $ chain 1)
      , Single "10"    (basic countSG $ chain 10)
      , Single "100"   (basic countSG $ chain 100)
      , Single "1000"  (basic countSG $ chain 1000)
      , Single "10000" (basic countSG $ chain 10000)
      ]
  , Group "components_connected"
      [ Single "1"     (basic countComps $ chain 1)
      , Single "10"    (basic countComps $ chain 10)
      , Single "100"   (basic countComps $ chain 100)
      , Single "1000"  (basic countComps $ chain 1000)
      , Single "10000" (basic countComps $ chain 10000)
      ]
  , Group "components_seq"
      [ Single "1"     (basic countComps $ seq 1)
      , Single "10"    (basic countComps $ seq 10)
      , Single "100"   (basic countComps $ seq 100)
      , Single "1000"  (basic countComps $ seq 1000)
      , Single "10000" (basic countComps $ seq 10000)
      ]
  , Group "components_disconnected"
      [ Single "1"     (basic countComps $ disc 1)
      , Single "10"    (basic countComps $ disc 10)
      , Single "100"   (basic countComps $ disc 100)
      , Single "1000"  (basic countComps $ disc 1000)
      , Single "10000" (basic countComps $ disc 10000)
      ]
  , Group "bicomponents_chain"
      [ Single "1"     (basic countBicomps $ chain 1)
      , Single "10"    (basic countBicomps $ chain 10)
      , Single "100"   (basic countBicomps $ chain 100)
      , Single "1000"  (basic countBicomps $ chain 1000)
      , Single "10000" (basic countBicomps $ chain 10000)
      ]
  , Group "bicomponents_seq"
      [ Single "1"     (basic countBicomps $ seq 1)
      , Single "10"    (basic countBicomps $ seq 10)
      , Single "100"   (basic countBicomps $ seq 100)
      , Single "1000"  (basic countBicomps $ seq 1000)
      , Single "10000" (basic countBicomps $ seq 10000)
      ]
  , Group "bicomponents_disconnected"
      [ Single "1"     (basic countBicomps $ disc 1)
      , Single "10"    (basic countBicomps $ disc 10)
      , Single "100"   (basic countBicomps $ disc 100)
      , Single "1000"  (basic countBicomps $ disc 1000)
      , Single "10000" (basic countBicomps $ disc 10000)
      ]
  ]

main : IO ()
main = runDefault (const True) Table show bench
