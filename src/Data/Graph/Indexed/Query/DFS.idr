||| This modules provides several functions for traversing
||| graphs in depth-first order and accumulating results in
||| various ways along the way.
module Data.Graph.Indexed.Query.DFS

import Data.Either
import Data.Tree
import Data.Graph.Indexed
import Data.Graph.Indexed.Query.Util
import Data.Graph.Indexed.Query.Visited

%default total

parameters {k : Nat}
           (g : IGraph k e n)

--------------------------------------------------------------------------------
-- Flat DFS traversals
--------------------------------------------------------------------------------

  -- flat DFS implementation for large graphs
  dfsL : List (Fin k) -> (s -> Fin k -> Either s a) -> s -> MVis k (Either s a)
  dfsL []      f st r t = Left st # t
  dfsL (x::xs) f st r t =
    let False # t := mvisited r x t | True # t => dfsL xs f st (assert_smaller r r) t
        Left st2  := f st x | Right v => Right v # t
     in dfsL (neighbours g x ++ xs) f st2 (assert_smaller r r) (mvisit r x t)

  -- flat DFS implementation for small graphs
  dfsS : List (Fin k) -> (s -> Fin k -> Either s a) -> s -> Vis k (Either s a)
  dfsS []      f st v = (Left st, v)
  dfsS (x::xs) f st v =
    if visited x v then dfsS xs f st v
    else
      let Left st2 := f st x | Right x => (Right x, v)
       in dfsS (neighbours g x ++ xs) f st2 (assert_smaller v $ visit x v)

  %inline dfsL' : List (Fin k) -> (s -> Fin k -> s) -> s -> MVis k s
  dfsL' xs acc i r t = fromLeftMVis $ dfsL xs (fleft2 acc) i r t

  -- flat DFS implementation for small graphs
  %inline dfsS' : List (Fin k) -> (s -> Fin k -> s) -> s -> Vis k s
  dfsS' xs acc i v = fromLeftVis $ dfsS xs (fleft2 acc) i v

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
       (taboo : List (Fin k))
    -> (s -> Fin k -> Either s a)
    -> (init : s)
    -> Fin k
    -> Either s a
  limitedDfsWith taboo acc init x =
    if k < 64
       then fst $ dfsS [x] acc init (visitAll taboo ini)
       else visiting k $ (\r => dfsL [x] acc init r . mvisitAll r taboo)

  ||| Traverses the graph in depth-first order from the given
  ||| start node and accumulates the nodes encountered with the
  ||| given function.
  |||
  ||| This abborts if the function returns a `Right`, otherwise it
  ||| continues with the traversal. The result is either the
  ||| accumulated state or the final result (if any).
  export %inline
  dfsWith : (s -> Fin k -> Either s a) -> (init : s) -> Fin k -> Either s a
  dfsWith = limitedDfsWith []

  ||| Like `dfsWith` but accumulates the whole connected component
  ||| from the given starting node in depth-first order.
  export %inline
  limitedDfsWith' :
       (taboo : List (Fin k))
    -> (acc : s -> Fin k -> s)
    -> (init : s)
    -> Fin k
    -> s
  limitedDfsWith' taboo acc init =
    fromLeft . limitedDfsWith taboo (fleft2 acc) init

  ||| Like `dfsWith` but accumulates the whole connected component
  ||| from the given starting node in depth-first order.
  export %inline
  dfsWith' : (acc : s -> Fin k -> s) -> (init : s) -> Fin k -> s
  dfsWith' = limitedDfsWith' []

  ||| Traverses the graph in depth-first order for the given start nodes
  ||| returning the encountered nodes in a `SnocList`.
  export %inline
  limitedDfs : (taboo : List (Fin k)) -> Fin k -> SnocList (Fin k)
  limitedDfs taboo = limitedDfsWith' taboo (:<) [<]

  ||| Traverses the graph in depth-first order for the given start nodes
  ||| returning the encountered nodes in a `SnocList`.
  export %inline
  dfs : Fin k -> SnocList (Fin k)
  dfs = limitedDfs []

--------------------------------------------------------------------------------
-- Component-wise DFS traversals
--------------------------------------------------------------------------------

  -- flat component-wise DFS implementation for large graphs
  cdfsL : (s -> Fin k -> s) -> s -> SnocList s -> List (Fin k) -> MVis k (List s)
  cdfsL f i ss []      r t = (ss <>> []) # t
  cdfsL f i ss (x::xs) r t =
    let False # t := mvisited r x t | True # t => cdfsL f i ss xs r t
        y # t     := dfsL' [x] f i r t
     in cdfsL f i (ss:<y) xs r t

  -- flat component-wise DFS implementation for small graphs
  cdfsS : (s -> Fin k -> s) -> s -> SnocList s -> List (Fin k) -> Vis k (List s)
  cdfsS f i ss []      v = (ss <>> [], v)
  cdfsS f i ss (x::xs) v =
    if visited x v then cdfsS f i ss xs v
    else let (y,v2) := dfsS' [x] f i v in cdfsS f i (ss:<y) xs v2

  ||| Traverses the graph in depth-first order for the given
  ||| start nodes and accumulates the nodes encountered with the
  ||| given function.
  |||
  ||| Unlike with `dfsWith`, results are accumulated component-wise,
  ||| using initial state `init` for every component we encounter.
  export
  cdfsWith : (acc : s -> Fin k -> s) -> (init : s) -> List (Fin k) -> List s
  cdfsWith acc init xs =
    if k < 64
       then fst $ cdfsS acc init [<] xs ini
       else visiting k (cdfsL acc init [<] xs)

  ||| Traverses the whole graph in depth-first order
  ||| accumulates the nodes encountered with the given function.
  export %inline
  cdfsWith' : (acc : s -> Fin k -> s) -> (init : s) -> List s
  cdfsWith' acc init = cdfsWith acc init (allFinsFast k)

  ||| Traverses the graph in depth-first order for the given start nodes
  ||| returning the encountered nodes in a `SnocList`.
  export %inline
  cdfs : List (Fin k) -> List (SnocList (Fin k))
  cdfs = cdfsWith (:<) [<]

  ||| Traverses the whole graph in depth-first order
  ||| returning the encountered nodes in a `SnocList`.
  export %inline
  cdfs' : List (SnocList (Fin k))
  cdfs' = cdfsWith' (:<) [<]

--------------------------------------------------------------------------------
-- Tree-shaped DFS traversals
--------------------------------------------------------------------------------

  -- tree-based DFS implementation for large graphs
  dffL : (Fin k -> s) -> List (Fin k) -> MVis k (Forest s)
  dffL f []      r t = [] # t
  dffL f (x::xs) r t =
      let False # t := mvisited r x t
            | True # t => dffL f xs (assert_smaller r r) t
          ts # t := dffL f (neighbours g x) (assert_smaller r r) (mvisit r x t)
          fs # t := dffL f xs (assert_smaller r r) t
       in (T (f x) ts :: fs) # t

  -- tree-based DFS implementation for small graphs
  dffS : (Fin k -> t) -> List (Fin k) -> Visited k -> (Forest t, Visited k)
  dffS f []      v = ([], v)
  dffS f (x::xs) v =
    if visited x v then dffS f xs v
    else
      let (ts,v2) := dffS f (neighbours g x) (assert_smaller v $ visit x v)
          (fs,v3) := dffS f xs (assert_smaller v v2)
       in (T (f x) ts :: fs, v3)

  ||| Traverses the graph in depth-first order for the given
  ||| start nodes and converts the nodes encountered with the
  ||| given function.
  |||
  ||| Unlike `dfsWith`, this returns a forest of spanning trees
  ||| of the connected components encountered.
  export
  dffWith : (Fin k -> t) -> List (Fin k) -> Forest t
  dffWith f xs =
    if k < 64
       then fst $ dffS f xs ini
       else visiting k $ \t => dffL f xs t

  ||| Traverses the whole graph in depth-first order
  ||| converts the nodes encountered with the given function.
  |||
  ||| Unlike `dfsWith'`, this returns a forest of spanning trees
  ||| of the connected components encountered.
  export %inline
  dffWith' : (Fin k -> t) -> Forest t
  dffWith' f = dffWith f (allFinsFast k)

  ||| Traverses the graph in depth-first order for the given start nodes
  ||| returning the encountered nodes in a list.
  |||
  ||| Unlike `dfs`, this returns a forest of spanning trees
  ||| of the connected components encountered.
  export %inline
  dff : List (Fin k) -> Forest (Fin k)
  dff = dffWith id

  ||| Traverses the whole graph in depth-first order
  ||| returning the encountered nodes in a list.
  |||
  ||| Unlike `dfs'`, this returns a forest of spanning trees
  ||| of the connected components encountered.
  export %inline
  dff' : Forest (Fin k)
  dff' = dffWith' id

--------------------------------------------------------------------------------
-- ALGORITHMS BASED ON DFS
--------------------------------------------------------------------------------

  ||| Collection of connected components
  export %inline
  components : List (SnocList $ Fin k)
  components = cdfs'

  ||| Number of connected components
  export %inline
  noComponents : Nat
  noComponents = length components

  ||| Is the graph connected?
  export %inline
  isConnected : Bool
  isConnected = noComponents == 1
