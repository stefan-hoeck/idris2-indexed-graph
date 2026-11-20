module Data.Graph.Indexed.Query.BFS

import Data.Queue
import Data.Graph.Indexed
import Data.Graph.Indexed.Query.Util
import Data.Graph.Indexed.Query.Visited
import Data.SnocList

%default total

enqueueE :
     Queue (s, Node g)
  -> (s -> Node g -> Either s a)
  -> s
  -> List (Node g)
  -> Either (Queue (s, Node g)) a
enqueueE q f st []      = Left q
enqueueE q f st (x::xs) =
  case f st x of
    Right v => Right v
    Left st2 => enqueueE (enqueue q (st2, x)) f st xs

parameters (g : Graph e n)

--------------------------------------------------------------------------------
-- Flat BFS traversals
--------------------------------------------------------------------------------

  -- flat BFS implementation for large graphs
  bfsL : Queue (s,Node g) -> (s -> Node g -> Either s a) -> MVis t g (Maybe a)
  bfsL q f r t =
    case dequeue q of
      Nothing => Nothing # t
      Just ((vs,x),q2) =>
       let False # t := mvisited r x t
             | True # t => bfsL q2 f (assert_smaller r r) t
           Left q3 := enqueueE q2 f vs (neighbours x) | Right v => Just v # t
           _ # t := mvisit r x t
        in bfsL q3 f (assert_smaller r r) t

  ||| Traverses the graph in breadth-first order for the given
  ||| start nodes and accumulates the nodes encountered with the
  ||| given function.
  |||
  ||| Unlike `bfsWith`, this takes a list of nodes that are taboo, that is
  ||| that will already be set to `visited`. This allows us exclude certain
  ||| pathways from our search.
  |||
  ||| One use case is to find the shortest cycle containing a given
  ||| edge or sequence of edges.
  export
  limitedBfsWith :
       (taboo : List (Node g))
    -> (s -> Node g -> Either s a)
    -> (init : s)
    -> Node g
    -> Maybe a
  limitedBfsWith taboo acc init x =
    visiting g $ \r,t =>
      let _ # t := mvisitAll r taboo t
       in bfsL (fromList [(init,x)]) acc r t

  ||| Traverses the graph in breadth-first order for the given
  ||| start nodes and accumulates the nodes encountered with the
  ||| given function.
  export %inline
  bfsWith : (s -> Node g -> Either s a) -> (init : s) -> Node g -> Maybe a
  bfsWith = limitedBfsWith []

  ||| Tries to find a shortest path between the two nodes.
  export %inline
  limitedBfs :
       (taboo : List (Node g))
     -> Node g
     -> Node g
     -> Maybe (SnocList (Node g))
  limitedBfs taboo start end =
    if start == end then Just [< start]
    else
      limitedBfsWith
        taboo
        (\sx,x => if x == end then Right (sx :< x) else Left (sx :< x))
        [<start]
        start

  ||| Tries to find a shortest path between the two nodes.
  export %inline
  bfs : Node g -> Node g -> Maybe (SnocList (Node g))
  bfs = limitedBfs []

----------------------------------------------------------------------------------
---- Generalized Breadth-First Searches
----------------------------------------------------------------------------------

  -- BFS implementation covering a whole connected component for large graphs
  bfsAllL : SnocList s -> Queue (s,Node g) -> (s -> Node g -> s) -> MVis t g (List s)
  bfsAllL ss q f r t =
    case dequeue q of
      Nothing => (ss <>> []) # t
      Just ((vs,x),q2) =>
       let False # t := mvisited r x t
             | True # t => bfsAllL ss q2 f (assert_smaller r r) t
           q3 := enqueueAll q2 (map (\y => (f vs y, y)) $ neighbours x)
           _ # t := mvisit r x t
        in bfsAllL (ss :< vs) q3 f (assert_smaller r r) t

  ||| Traverses the graph in breadth-first order for the given
  ||| start nodes and accumulates the nodes encountered with the
  ||| given function.
  export
  bfsAllWith : (s -> Node g -> s) -> (init : s) -> Node g -> List s
  bfsAllWith acc init x =
    visiting g (bfsAllL [<] (fromList [(init,x)]) acc)

  export
  distancesToNode : Node g -> List (Nat, Node g)
  distancesToNode x = bfsAllWith (\x,y => (S $ fst x, y)) (0,x) x

----------------------------------------------------------------------------------
---- Shortest Paths
----------------------------------------------------------------------------------

  covering
  shortestL :
       SnocList (SnocList $ Node g)
    -> Queue (SnocList $ Node g)
    -> MVis t g (List (SnocList $ Node g))
  shortestL sp q r t =
    case dequeue q of
      Nothing => (sp <>> []) # t
      Just (sx@(_:<x),q2) =>
        let False # t := mvisited r x t | True # t => shortestL sp q2 r t
            ns := map (sx :<) (neighbours x)
            _ # t := mvisit r x t
         in shortestL (sp :< sx) (enqueueAll q2 ns) r t
      Just (_,q2) => shortestL sp q2 r t

  ||| Computes the shortest paths to all nodes reachable from
  ||| the given starting node. This is a simplified version of
  ||| Dijkstra's algorithm for unweighted edges.
  |||
  ||| Runs in O(n+m) time and O(n) memory.
  export
  shortestPaths : Node g -> List (SnocList $ Node g)
  shortestPaths x =
    let q := fromList $ map ([<x] :<) (neighbours x)
     in assert_total $
          visiting g $ \r,t => let _ # t := mvisit r x t in shortestL [<] q r t
