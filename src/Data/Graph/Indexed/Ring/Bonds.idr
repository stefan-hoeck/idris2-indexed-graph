module Data.Graph.Indexed.Ring.Bonds

import Data.SortedSet
import Data.Graph.Indexed
import Data.Graph.Indexed.Ring.Util
import Data.Graph.Indexed.Subgraph

%default total

parameters {k : Nat}
           (g : IGraph k e n)

  ||| Adds the edges of a subgraph to an edge set
  export
  addEdges : EdgeSet k -> Subgraph k e n -> EdgeSet k
  addEdges x (G o h) =
    foldl (\s,(E a b _) => addEdge s (origin h a) (origin h b)) x $ edges h

  ||| Computes the cyclic bonds in a graph.
  |||
  ||| This justs collects the edges from the biconnected components.
  export
  ringBonds : EdgeSet k
  ringBonds = foldl addEdges empty (biconnectedComponents g)
