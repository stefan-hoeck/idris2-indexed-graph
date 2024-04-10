module Data.Graph.Indexed.Query.BFS

import Data.Queue
import Data.Graph.Indexed
import Data.Graph.Indexed.Query.Util
import Data.Graph.Indexed.Query.Visited
import Data.SnocList

%default total

parameters {k : Nat}
           (g : IGraph k e n)

--------------------------------------------------------------------------------
-- Flat BFS traversals
--------------------------------------------------------------------------------

  -- flat BFS implementation for large graphs
  bfsL :
       Queue (Nat,Fin k)
    -> (s -> Nat -> Fin k -> Either s a)
    -> s
    -> MVis k (Either s a)
  bfsL q f st v =
    case dequeue q of
      Nothing     => Left st # v
      Just ((d,x),q2) =>
       let False # v2 := mvisited x v
             | True # v2 => bfsL q2 f st (assert_smaller v v2)
           q3         := enqueueAll q2 $ (S d,) <$> neighbours g x
           Left st2   := f st d x | Right v => Right v # v2
        in bfsL q3 f st2 (assert_smaller v $ mvisit x v2)

  -- flat BFS implementation for small graphs
  bfsS :
       Queue (Nat,Fin k)
    -> (s -> Nat -> Fin k -> Either s a)
    -> s
    -> Vis k (Either s a)
  bfsS q f st v =
    case dequeue q of
      Nothing     => (Left st,v)
      Just ((d,x),q2) =>
       let False    := visited x v | True => bfsS q2 f st (assert_smaller v v)
           q3       := enqueueAll q2 ((S d,) <$> neighbours g x)
           Left st2 := f st d x | Right x => (Right x, v)
        in bfsS q3 f st2 (assert_smaller v $ visit x v)

  %inline bfsL' : Queue (Nat,Fin k) -> (s -> Nat -> Fin k -> s) -> s -> MVis k s
  bfsL' xs acc i v = fromLeftMVis $ bfsL xs (fleft3 acc) i v

  -- flat BFS implementation for small graphs
  %inline bfsS' : Queue (Nat,Fin k) -> (s -> Nat -> Fin k -> s) -> s -> Vis k s
  bfsS' xs acc i v = fromLeftVis $ bfsS xs (fleft3 acc) i v

  ||| Traverses the graph in breadth-first order for the given
  ||| start nodes and accumulates the nodes encountered with the
  ||| given function.
  export
  bfsWith :
       (s -> Nat -> Fin k -> Either s a)
    -> (init : s)
    -> Fin k
    -> Either s a
  bfsWith acc init x =
    if k < 64
       then fst $ bfsS (fromList [(0,x)]) acc init ini
       else visiting' k (bfsL (fromList [(0,x)]) acc init)

  ||| Traverses the whole graph in breadth-first order
  ||| accumulating the nodes encountered with the given function.
  export %inline
  bfsWith' : (acc : s -> Nat -> Fin k -> s) -> (init : s) -> Fin k -> s
  bfsWith' acc init = fromLeft . bfsWith (fleft3 acc) init

  ||| Traverses the whole graph in breadth-first order
  ||| returning the encountered nodes in a `SnocList`.
  export %inline
  bfs : Fin k -> SnocList (Nat,Fin k)
  bfs = bfsWith' (\st,n,x => st :< (n,x)) [<]

--------------------------------------------------------------------------------
-- Shortest Path Algorithms
--------------------------------------------------------------------------------

  covering
  shortestL :
       SnocList (SnocList $ Fin k)
    -> Queue (SnocList $ Fin k)
    -> MVis k (List (SnocList $ Fin k))
  shortestL sp q v =
    case dequeue q of
      Nothing => (sp <>> []) # v
      Just (sx@(_:<x),q2) =>
        let False # v2 := mvisited x v | True # v2 => shortestL sp q2 v2
            ns := map (sx :<) (neighbours g x)
         in shortestL (sp :< sx) (enqueueAll q2 ns) (mvisit x v2)
      Just (_,q2) => shortestL sp q2 v

  covering
  shortestS :
       SnocList (SnocList $ Fin k)
    -> Queue (SnocList $ Fin k)
    -> Vis k (List (SnocList $ Fin k))
  shortestS sp q v =
    case dequeue q of
      Nothing => (sp <>> [],v)
      Just (sx@(_:<x),q2) => case x `visited` v of
        True  => shortestS sp q2 v
        False =>
          let ns := map (sx :<) (neighbours g x)
           in shortestS (sp :< sx) (enqueueAll q2 ns) (x `visit` v)
      Just (_,q2) => shortestS sp q2 v

  ||| Computes the shortest paths to all nodes reachable from
  ||| the given starting node. This is a simplified version of
  ||| Dijkstra's algorithm for unweighted edges.
  |||
  ||| Runs in O(n+m) time and O(n) memory.
  export
  shortestPaths : Fin k -> List (SnocList $ Fin k)
  shortestPaths x =
    let q := fromList $ map ([<x] :<) (neighbours g x)
     in assert_total $ if k < 64
          then fst $ shortestS [<] q (x `visit` ini)
          else visiting' k (\v => shortestL [<] q (x `mvisit` v))

  covering
  shortestL' :
       (target : Fin k)
    -> SnocList (SnocList $ Fin k)
    -> Queue (SnocList $ Fin k)
    -> MVis k (List (SnocList $ Fin k))
  shortestL' t sp q v =
    case dequeue q of
      Nothing => ([]) # v
      Just (sx@(_:<x),q2) => if x == t then ([sx]) # v else
        let False # v2 := mvisited x v | True # v2 => shortestL' t sp q2 v2
            ns := map (sx :<) (neighbours g x)
         in shortestL' t (sp :< sx) (enqueueAll q2 ns) (mvisit x v2)
      Just (_,q2) => shortestL' t sp q2 v

  covering
  shortestS' :
       (target : Fin k)
    -> SnocList (SnocList $ Fin k)
    -> Queue (SnocList $ Fin k)
    -> Vis k (List (SnocList $ Fin k))
  shortestS' t sp q v =
    case dequeue q of
      Nothing => ([],v)
      Just (sx@(_:<x),q2) => case x == t of
        True  => ([sx],v)
        False => case x `visited` v of
          True  => shortestS' t sp q2 v
          False =>
            let ns := map (sx :<) (neighbours g x)
             in shortestS' t (sp :< sx) (enqueueAll q2 ns) (x `visit` v)
      Just (_,q2) => shortestS' t sp q2 v

  ||| Computes the shortest paths to a specific node reachable from
  ||| the given starting node. Should be less time consuming than computing all
  ||| possible shortest paths from a start node and then filter this list until
  ||| finding the only entry with the target node.
  |||
  ||| If there is no connection of the start and traget node, an empty list is
  ||| returned.
  |||
  ||| Runs in O(n+m) time and O(n) memory.
  export
  shortestPathTo : (start,target : Fin k) -> List (Fin k)
  shortestPathTo x t =
    let q := fromList $ map ([<x] :<) (neighbours g x)
     in assert_total $ if k < 64
          then foldl (\acc,e => acc ++ (e <>> [])) []
                     (fst $ shortestS' t [<] q (x `visit` ini))
          else foldl (\acc,e => acc ++ (e <>> [])) []
                     (visiting' k (\v => shortestL' t [<] q (x `mvisit` v)))
