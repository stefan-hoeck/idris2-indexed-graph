module Data.Graph.Indexed.Query.BFS

import Data.Queue
import Data.Graph.Indexed
import Data.Graph.Indexed.Query.Util
import Data.Graph.Indexed.Query.Visited

%default total

parameters {k : Nat}
           (g : IGraph k e n)

  -- TODO: this should be dropped and `neighbours` and `lneighbours` adjusted
  %inline nbours : Fin k -> List (Fin k)
  nbours x = keys $ neighbours g x

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
           q3         := enqueueAll q2 $ (S d,) <$> nbours x
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
           q3       := enqueueAll q2 ((S d,) <$> nbours x)
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
