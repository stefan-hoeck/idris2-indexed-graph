||| This modules provides several functions for traversing
||| graphs in depth-first order and accumulating results in
||| various ways along the way.
module Data.Graph.Indexed.Query.DFS

import Data.Tree
import Data.Graph.Indexed
import Data.Graph.Indexed.Query.Visited

%default total

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- Internal alias for stateful functions when visiting small graphs
0 Vis : Nat -> Type -> Type
Vis k s = Visited k -> (s, Visited k)

-- Internal alias for stateful functions when visiting large graphs
0 MVis : Nat -> Type -> Type
MVis k s = MVisited k -@ CRes s (MVisited k)

parameters {k : Nat}
           (g : IGraph k e n)

  -- TODO: this should be dropped and `neighbours` and `lneighbours` adjusted
  %inline nbours : Fin k -> List (Fin k)
  nbours x = keys $ neighbours g x

--------------------------------------------------------------------------------
-- Flat DFS traversals
--------------------------------------------------------------------------------

  -- flat DFS implementation for large graphs
  dfsL : List (Fin k) -> (s -> Fin k -> s) -> s -> MVis k s
  dfsL []      f st v = st # v
  dfsL (x::xs) f st v =
    let False # v2 := mvisited x v
          | True # v2 => dfsL xs f st (assert_smaller v v2)
     in dfsL (nbours x ++ xs) f (f st x) (assert_smaller v $ mvisit x v2)

  -- flat DFS implementation for small graphs
  dfsS : List (Fin k) -> (s -> Fin k -> s) -> s -> Vis k s
  dfsS []      f st v = (st, v)
  dfsS (x::xs) f st v =
    if visited x v then dfsS xs f st v
    else dfsS (nbours x ++ xs) f (f st x) (assert_smaller v $ visit x v)

  ||| Traverses the graph in depth-first order for the given
  ||| start nodes and accumulates the nodes encountered with the
  ||| given function.
  export
  dfsWith : (acc : s -> Fin k -> s) -> (init : s) -> List (Fin k) -> s
  dfsWith acc init xs =
    if k < 64
       then fst $ dfsS xs acc init ini
       else visiting' k (dfsL xs acc init)

  ||| Traverses the whole graph in depth-first order
  ||| accumulates the nodes encountered with the given function.
  export %inline
  dfsWith' : (acc : s -> Fin k -> s) -> (init : s) -> s
  dfsWith' acc init = dfsWith acc init (allFinsFast k)

  ||| Traverses the graph in depth-first order for the given start nodes
  ||| returning the encountered nodes in a `SnocList`.
  export %inline
  dfs : List (Fin k) -> SnocList (Fin k)
  dfs = dfsWith (:<) [<]

  ||| Traverses the whole graph in depth-first order
  ||| returning the encountered nodes in a `SnocList`.
  export %inline
  dfs' : SnocList (Fin k)
  dfs' = dfsWith' (:<) [<]

--------------------------------------------------------------------------------
-- Component-wise DFS traversals
--------------------------------------------------------------------------------

  -- flat component-wise DFS implementation for large graphs
  cdfsL : (s -> Fin k -> s) -> s -> SnocList s -> List (Fin k) -> MVis k (List s)
  cdfsL f i ss []      v = (ss <>> []) # v
  cdfsL f i ss (x::xs) v =
    let False # v2 := mvisited x v | True # v2 => cdfsL f i ss xs v2
        y # v3     := dfsL [x] f i v2
     in cdfsL f i (ss:<y) xs v3

  -- flat component-wise DFS implementation for small graphs
  cdfsS : (s -> Fin k -> s) -> s -> SnocList s -> List (Fin k) -> Vis k (List s)
  cdfsS f i ss []      v = (ss <>> [], v)
  cdfsS f i ss (x::xs) v =
    if visited x v then cdfsS f i ss xs v
    else let (y,v2) := dfsS [x] f i v in cdfsS f i (ss:<y) xs v2

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
       else visiting' k (cdfsL acc init [<] xs)

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
  dffL : (Fin k -> t) -> List (Fin k) -> MVisited k -@ CRes (Forest t) (MVisited k)
  dffL f []      v = [] # v
  dffL f (x::xs) v =
      let False # v2 := mvisited x v
            | True # v2 => dffL f xs (assert_smaller v v2)
          ts # v3 := dffL f (nbours x) (assert_smaller v $ mvisit x v2)
          fs # v4 := dffL f xs (assert_smaller v v3)
       in (T (f x) ts :: fs) # v4

  -- tree-based DFS implementation for small graphs
  dffS : (Fin k -> t) -> List (Fin k) -> Visited k -> (Forest t, Visited k)
  dffS f []      v = ([], v)
  dffS f (x::xs) v =
    if visited x v then dffS f xs v
    else
      let (ts,v2) := dffS f (nbours x) (assert_smaller v $ visit x v)
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
       else visiting k $ \v => let fs # v2 := dffL f xs v in done fs v2

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
  isConnected : Bool
  isConnected = noComponents == 1
