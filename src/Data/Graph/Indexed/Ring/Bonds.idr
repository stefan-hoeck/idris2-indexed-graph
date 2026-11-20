module Data.Graph.Indexed.Ring.Bonds

import Data.SortedSet
import Data.Graph.Indexed
import Data.Graph.Indexed.Ring.Util
import Data.Graph.Indexed.Subgraph

%default total

parameters (g : Graph e n)

  ||| Adds the edges of a subgraph to an edge set
  export
  addEdges : EdgeSet g -> Subgraph g -> EdgeSet g
  addEdges x h =
    foldl (\s,(E a b _) => addEdge s (origin $ N a) (origin $ N b)) x $ edges h

  ||| Computes the cyclic bonds in a graph.
  |||
  ||| This justs collects the edges from the biconnected components.
  export
  ringBonds : EdgeSet g
  ringBonds = foldl addEdges empty (biconnectedComponents g)
