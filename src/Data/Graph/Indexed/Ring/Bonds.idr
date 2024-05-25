module Data.Graph.Indexed.Ring.Bonds

import Data.SortedSet
import Data.Graph.Indexed
import Data.Graph.Indexed.Subgraph

%default total

||| A set of unlabeled edges of order `k`
public export
0 EdgeSet : (k : Nat) -> Type
EdgeSet k = SortedSet (Edge k ())

parameters {k : Nat}
           (g : IGraph k e n)

  ||| Adds the edges of a subgraph to an edge set
  export
  addEdges : EdgeSet k -> Subgraph k e n -> EdgeSet k
  addEdges x (G o h) =
    foldl (\s => maybe s (\x => insert (ignore x) s) . originEdge h) x $ edges h

  ||| Computes the cyclic bonds in a graph.
  |||
  ||| This justs collects the edges from the biconnected components.
  export
  ringBonds : EdgeSet k
  ringBonds = foldl addEdges empty (biconnectedComponents g)
