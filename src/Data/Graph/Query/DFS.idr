||| This modules provides several functions for traversing
||| graphs in depth-first order and accumulating results in
||| various ways along the way.
module Data.Graph.Query.DFS

import Data.Either
import Data.Tree
import Data.Graph
import Data.Graph.Query.Util
import Data.Graph.Query.Visited

%default total

parameters (g : Graph e n)

--------------------------------------------------------------------------------
-- Flat DFS traversals
--------------------------------------------------------------------------------

  -- flat DFS implementation for large graphs
  dfsL : Nodes g -> (s -> Node g -> Either s a) -> s -> MVis t g (Either s a)
  dfsL []      f st r t = Left st # t
  dfsL (x::xs) f st r t =
    let False # t := mvisited r x t | True # t => dfsL xs f st (assert_smaller r r) t
        Left st2  := f st x | Right v => Right v # t
        _ # t     := mvisit r x t
     in dfsL (neighbours x ++ xs) f st2 (assert_smaller r r) t

  %inline dfsL' : Nodes g -> (s -> Node g -> s) -> s -> MVis t g s
  dfsL' xs acc i r t = fromLeftMVis $ dfsL xs (fleft2 acc) i r t

  ||| Traverses the graph in depth-first order from the given
  ||| start node and accumulates the nodes encountered with the
  ||| given function.
  |||
  ||| This abborts if the function returns a `Right`, otherwise it
  ||| continues with the traversal. The result is either the
  ||| accumulated state or the final result (if any).
  |||
  ||| Unlike `dfsWith`, this takes a list of nodes that are taboo, that is
  ||| that will already be set to `visited`. This allows us exclude certain
  ||| pathways from our search.
  export
  limitedDfsWith :
       (taboo : Nodes g)
    -> (s -> Node g -> Either s a)
    -> (init : s)
    -> Node g
    -> Either s a
  limitedDfsWith taboo acc init x =
    visiting g $ \r,t =>
      let _ # t := mvisitAll r taboo t
       in dfsL [x] acc init r t

  ||| Traverses the graph in depth-first order from the given
  ||| start node and accumulates the nodes encountered with the
  ||| given function.
  |||
  ||| This abborts if the function returns a `Right`, otherwise it
  ||| continues with the traversal. The result is either the
  ||| accumulated state or the final result (if any).
  export %inline
  dfsWith : (s -> Node g -> Either s a) -> (init : s) -> Node g -> Either s a
  dfsWith = limitedDfsWith []

  ||| Like `dfsWith` but accumulates the whole connected component
  ||| from the given starting node in depth-first order.
  export %inline
  limitedDfsWith' :
       (taboo : Nodes g)
    -> (acc : s -> Node g -> s)
    -> (init : s)
    -> Node g
    -> s
  limitedDfsWith' taboo acc init =
    fromLeft . limitedDfsWith taboo (fleft2 acc) init

  ||| Like `dfsWith` but accumulates the whole connected component
  ||| from the given starting node in depth-first order.
  export %inline
  dfsWith' : (acc : s -> Node g -> s) -> (init : s) -> Node g -> s
  dfsWith' = limitedDfsWith' []

  ||| Traverses the graph in depth-first order for the given start nodes
  ||| returning the encountered nodes in a `SnocList`.
  export %inline
  limitedDfs : (taboo : Nodes g) -> Node g -> Sedon g
  limitedDfs taboo = limitedDfsWith' taboo (:<) [<]

  ||| Traverses the graph in depth-first order for the given start nodes
  ||| returning the encountered nodes in a `SnocList`.
  export %inline
  dfs : Node g -> Sedon g
  dfs = limitedDfs []

--------------------------------------------------------------------------------
-- Component-wise DFS traversals
--------------------------------------------------------------------------------

  -- flat component-wise DFS implementation for large graphs
  cdfsL : (s -> Node g -> s) -> s -> SnocList s -> Nodes g -> MVis t g (List s)
  cdfsL f i ss []      r t = (ss <>> []) # t
  cdfsL f i ss (x::xs) r t =
    let False # t := mvisited r x t | True # t => cdfsL f i ss xs r t
        y # t     := dfsL' [x] f i r t
     in cdfsL f i (ss:<y) xs r t

  ||| Traverses the graph in depth-first order for the given
  ||| start nodes and accumulates the nodes encountered with the
  ||| given function.
  |||
  ||| Unlike with `dfsWith`, results are accumulated component-wise,
  ||| using initial state `init` for every component we encounter.
  export
  cdfsWith : (acc : s -> Node g -> s) -> (init : s) -> Nodes g -> List s
  cdfsWith acc init xs = visiting g (cdfsL acc init [<] xs)

  ||| Traverses the whole graph in depth-first order
  ||| accumulates the nodes encountered with the given function.
  export %inline
  cdfsWith' : (acc : s -> Node g -> s) -> (init : s) -> List s
  cdfsWith' acc init = cdfsWith acc init (nodes g)

  ||| Traverses the graph in depth-first order for the given start nodes
  ||| returning the encountered nodes in a `SnocList`.
  export %inline
  cdfs : Nodes g -> List (Sedon g)
  cdfs = cdfsWith (:<) [<]

  ||| Traverses the whole graph in depth-first order
  ||| returning the encountered nodes in a `SnocList`.
  export %inline
  cdfs' : List (Sedon g)
  cdfs' = cdfsWith' (:<) [<]

--------------------------------------------------------------------------------
-- Tree-shaped DFS traversals
--------------------------------------------------------------------------------

  -- tree-based DFS implementation for large graphs
  dffL : (Node g -> s) -> Nodes g -> MVis t g (Forest s)
  dffL f []      r t = [] # t
  dffL f (x::xs) r t =
      let False # t := mvisited r x t
            | True # t => dffL f xs (assert_smaller r r) t
          _  # t := mvisit r x t
          ts # t := dffL f (neighbours x) (assert_smaller r r) t
          fs # t := dffL f xs (assert_smaller r r) t
       in (T (f x) ts :: fs) # t

  ||| Traverses the graph in depth-first order for the given
  ||| start nodes and converts the nodes encountered with the
  ||| given function.
  |||
  ||| Unlike `dfsWith`, this returns a forest of spanning trees
  ||| of the connected components encountered.
  export
  dffWith : (Node g -> t) -> Nodes g -> Forest t
  dffWith f xs = visiting g (dffL f xs)

  ||| Traverses the whole graph in depth-first order
  ||| converts the nodes encountered with the given function.
  |||
  ||| Unlike `dfsWith'`, this returns a forest of spanning trees
  ||| of the connected components encountered.
  export %inline
  dffWith' : (Node g -> t) -> Forest t
  dffWith' f = dffWith f (nodes g)

  ||| Traverses the graph in depth-first order for the given start nodes
  ||| returning the encountered nodes in a list.
  |||
  ||| Unlike `dfs`, this returns a forest of spanning trees
  ||| of the connected components encountered.
  export %inline
  dff : Nodes g -> Forest (Node g)
  dff = dffWith id

  ||| Traverses the whole graph in depth-first order
  ||| returning the encountered nodes in a list.
  |||
  ||| Unlike `dfs'`, this returns a forest of spanning trees
  ||| of the connected components encountered.
  export %inline
  dff' : Forest (Node g)
  dff' = dffWith' id

--------------------------------------------------------------------------------
-- ALGORITHMS BASED ON DFS
--------------------------------------------------------------------------------

  ||| Collection of connected components
  export %inline
  components : List (Sedon g)
  components = cdfs'

  ||| Number of connected components
  export %inline
  noComponents : Nat
  noComponents = length components

  ||| Is the graph connected?
  export %inline
  isConnected : Bool
  isConnected = noComponents == 1
