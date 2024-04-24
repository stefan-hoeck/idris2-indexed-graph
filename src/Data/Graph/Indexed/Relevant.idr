module Data.Graph.Indexed.Relevant

import Data.Graph.Indexed
import Data.Graph.Indexed.Subgraph
import Data.Graph.Indexed.Query.Util
import Data.Graph.Indexed.Query.Visited
import Data.List
import Data.Queue
import Data.SnocList
import Debug.Trace
import Derive.Prelude

%default total
%language ElabReflection

||| A shortest path of length `length` from a starting node to node `last`.
||| Boolean `keep` indicates if all nodes are strictly smaller than
||| the starting node (according to an ordering `<`, where x < y means that
||| deg x <= deg y; this is the ordering `pi` given in the paper).
|||
||| Node `first` is the first node after the root node, and is used to
||| check if two paths are disjoint.
public export
record Path (k : Nat) where
  constructor P
  length : Nat
  keep   : Bool
  path   : SnocList (Fin k)
  first  : Fin k
  last   : Fin k

%runElab deriveIndexed "Path" [Show,Eq]

public export
0 Cycle : Nat -> Type
Cycle k = List (Fin k)

public export
0 ECycle : Nat -> Type
ECycle k = List (Fin k, Fin k)

revOnto : SnocList a -> SnocList a -> SnocList a
revOnto sx [<] = sx
revOnto sx (sy:<y) = revOnto (sx :< y) sy

toCycle : a -> SnocList a -> SnocList a -> List a
toCycle r sx sy = r :: (revOnto sx sy <>> [r])

parameters {k    : Nat}
           (g    : IGraph k e n)
           (root : Fin k)
           (rdeg : Nat)

  %inline smaller : Fin k -> Bool
  smaller n =
    case compare (deg g n) rdeg of
      LT => True
      EQ => root <= n
      GT => False

  init : Fin k -> Path k
  init n = P 1 (smaller n) [<n] n n

  append : Path k -> Fin k -> Path k
  append (P l kp p fs ls) n = P (S l) (kp && smaller n) (p :< n) fs n

  covering
  shortestL : SnocList (Path k) -> Queue (Path k) -> MVis k (List (Path k))
  shortestL sp q v =
    case dequeue q of
      Nothing => (sp <>> []) # v
      Just (p,q2) =>
        let False # v2 := mvisited p.last v | True # v2 => shortestL sp q2 v2
            ns  := map (append p) (neighbours g p.last)
            sp2 := if p.keep then sp :< p else sp
         in shortestL sp2 (enqueueAll q2 ns) (mvisit p.last v2)

  covering
--shortestS : SnocList (Path k) -> Queue (Path k) -> Visited k -> (List (Path k), Visited k)
  shortestS : SnocList (Path k) -> Queue (Path k) -> Vis k (List (Path k))
  shortestS sp q v =
    case dequeue q of
      Nothing => (sp <>> [],v)
      Just (p,q2) => case p.last `visited` v of
        True  => shortestS sp q2 v
        False =>
          let ns  := map (append p) (neighbours g p.last)
              sp2 := if p.keep then sp :< p else sp
           in shortestS sp2 (enqueueAll q2 ns) (p.last `visit` v)

  ||| Computes the shortest paths to all nodes reachable from
  ||| the given starting node. This is a simplified version of
  ||| Dijkstra's algorithm for unweighted edges.
  |||
  ||| Runs in O(n+m) time and O(n) memory.
  export
  shortestPaths : List (Path k)
  shortestPaths =
    let q := fromList $ map init (neighbours g root)
     in assert_total $ if k < 64
          then fst $ shortestS [<] q (root `visit` ini)
          else visiting' k (\v => shortestL [<] q (root `mvisit` v))

-- Takes a list of reverse paths starting all from the same node and
-- sorted by length (this is by construction: the `shortestPaths` algorithm
-- will produce shorter paths earlier than longer paths). It will pair every
-- path with all successors of equal length (resulting in odd cycles) and
-- one node longer (resulting in even cycles) and connect the pair if it
-- builds a proper, disjoint cycle.
mergePaths : {o : _} -> Fin o -> ISubgraph o k e n -> List (Path o) -> List (Cycle k)
mergePaths x g = go [<]
  where
    -- check if the two paths (their ending nodes are given explicitly) are
    -- connected via a bond but are otherwise disjoint
    %inline check : Path o -> Path o -> Bool
    check x y = x.first /= y.first && adjacent g x.last y.last

    %inline cycle : Path o -> Path o -> Cycle k
    cycle y z = fst . lab g <$> toCycle x y.path z.path

    addCs : SnocList (Cycle k) -> Path o -> List (Path o) -> SnocList (Cycle k)
    addCs sc p [] = sc
    addCs sc p (q::qs) =
      case S p.length >= q.length of
        False => sc
        True  => if check p q then addCs (sc :< cycle p q) p qs else addCs sc p qs

    -- for the current path, we take from the remaining paths those
    -- that are at most one node longer and try to pair them to
    -- form a cycle.
    go : SnocList (Cycle k) -> List (Path o) -> List (Cycle k)
    go sxs []        = sxs <>> []
    go sxs (p :: ps) = go (addCs sxs p ps) ps

-- We compute potentially relevant cycles by merging shortest
-- paths sharing the starting node. To make sure we compute each
-- cycle only once, we only consider shortest paths consisting
-- of nodes smaller than the starting node.
cycleSystem : {o : _} -> ISubgraph o k e n -> Fin o -> List (Cycle k)
cycleSystem g n = mergePaths n g (shortestPaths g n (deg g n))

findCycles : Subgraph k e n -> List (Cycle k)
findCycles (G 0 g) = []
findCycles (G (S k) g) =
  case filter ((2 <) . deg g) (nodes g) of
    [] => [Builtin.fst . lab g <$> (nodes g ++ [FZ])] -- this is already an elementary cycle
    ns => ns >>= cycleSystem g -- this is a system of cycles

-- cuts a graph into strongly connected components and computes
-- the potential relevant cycles for each component in isolation.
export
computeCI' : {k : _} -> IGraph k e n -> List (Cycle k)
computeCI' g = biconnectedComponents g >>= findCycles
