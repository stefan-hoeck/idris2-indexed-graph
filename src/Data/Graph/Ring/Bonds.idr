module Data.Graph.Ring.Bonds

import Data.SortedSet
import Data.Graph
import Data.Graph.Ring.Util
import Data.Graph.Subgraph

%default total

parameters (g : Graph e n)

  ||| Adds the edges of a subgraph to an edge set
  export
  addEdges : EdgeSet g -> Subgraph g -> EdgeSet g
  addEdges x h =
    foldl (\s,(LE a b _) => addEdge s (origin a) (origin b)) x $ edges h

  ||| Computes the cyclic bonds in a graph.
  |||
  ||| This justs collects the edges from the biconnected components.
  export
  ringBonds : EdgeSet g
  ringBonds = foldl addEdges empty (biconnectedComponents g)
