module Data.Graph.Indexed.Query.BFS

import Data.Queue
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
-- Flat BFS traversals
--------------------------------------------------------------------------------

  -- flat BFS implementation for large graphs
  bfsL : Queue (Fin k) -> (s -> Fin k -> s) -> s -> MVis k s
  bfsL q f st v =
    case dequeue q of
      Nothing     => st # v
      Just (x,q2) =>
       let False # v2 := mvisited x v
             | True # v2 => bfsL q2 f st (assert_smaller v v2)
           q3         := enqueueAll q2 (nbours x)
        in bfsL q3 f (f st x) (assert_smaller v $ mvisit x v2)

  -- flat BFS implementation for small graphs
  bfsS : Queue (Fin k) -> (s -> Fin k -> s) -> s -> Vis k s
  bfsS q f st v =
    case dequeue q of
      Nothing     => (st,v)
      Just (x,q2) =>
       let False := visited x v | True => bfsS q2 f st (assert_smaller v v)
           q3    := enqueueAll q2 (nbours x)
        in bfsS q3 f (f st x) (assert_smaller v $ visit x v)

  ||| Traverses the graph in depth-first order for the given
  ||| start nodes and accumulates the nodes encountered with the
  ||| given function.
  export
  bfsWith : (acc : s -> Fin k -> s) -> (init : s) -> List (Fin k) -> s
  bfsWith acc init xs =
    if k < 64
       then fst $ bfsS (fromList xs) acc init ini
       else visiting' k (bfsL (fromList xs) acc init)

  ||| Traverses the whole graph in depth-first order
  ||| accumulates the nodes encountered with the given function.
  export %inline
  bfsWith' : (acc : s -> Fin k -> s) -> (init : s) -> s
  bfsWith' acc init = bfsWith acc init (allFinsFast k)

  ||| Traverses the graph in depth-first order for the given start nodes
  ||| returning the encountered nodes in a `SnocList`.
  export %inline
  bfs : List (Fin k) -> SnocList (Fin k)
  bfs = bfsWith (:<) [<]

  ||| Traverses the whole graph in depth-first order
  ||| returning the encountered nodes in a `SnocList`.
  export %inline
  bfs' : SnocList (Fin k)
  bfs' = bfsWith' (:<) [<]

--------------------------------------------------------------------------------
-- Flat component-wise BFS traversals
--------------------------------------------------------------------------------

  -- flat component-wise DFS implementation for large graphs
  cbfsL : (s -> Fin k -> s) -> s -> SnocList s -> List (Fin k) -> MVis k (List s)
  cbfsL f i ss []      v = (ss <>> []) # v
  cbfsL f i ss (x::xs) v =
    let False # v2 := mvisited x v | True # v2 => cbfsL f i ss xs v2
        y # v3     := bfsL (fromList [x]) f i v2
     in cbfsL f i (ss:<y) xs v3

  -- flat component-wise DFS implementation for small graphs
  cbfsS : (s -> Fin k -> s) -> s -> SnocList s -> List (Fin k) -> Vis k (List s)
  cbfsS f i ss []      v = (ss <>> [], v)
  cbfsS f i ss (x::xs) v =
    if visited x v then cbfsS f i ss xs v
    else let (y,v2) := bfsS (fromList [x]) f i v in cbfsS f i (ss:<y) xs v2

  ||| Traverses the graph in depth-first order for the given
  ||| start nodes and accumulates the nodes encountered with the
  ||| given function.
  |||
  ||| Unlike with `bfsWith`, results are accumulated component-wise,
  ||| using initial state `init` for every component we encounter.
  export
  cbfsWith : (acc : s -> Fin k -> s) -> (init : s) -> List (Fin k) -> List s
  cbfsWith acc init xs =
    if k < 64
       then fst $ cbfsS acc init [<] xs ini
       else visiting' k (cbfsL acc init [<] xs)

  ||| Traverses the whole graph in depth-first order
  ||| accumulates the nodes encountered with the given function.
  export %inline
  cbfsWith' : (acc : s -> Fin k -> s) -> (init : s) -> List s
  cbfsWith' acc init = cbfsWith acc init (allFinsFast k)

  ||| Traverses the graph in depth-first order for the given start nodes
  ||| returning the encountered nodes in a `SnocList`.
  export %inline
  cbfs : List (Fin k) -> List (SnocList (Fin k))
  cbfs = cbfsWith (:<) [<]

  ||| Traverses the whole graph in depth-first order
  ||| returning the encountered nodes in a `SnocList`.
  export %inline
  cbfs' : List (SnocList (Fin k))
  cbfs' = cbfsWith' (:<) [<]
