module Data.Graph.Indexed.ShortestPath

import Data.Array.Mutable
import Data.List
import Data.Queue
import Derive.Prelude
import public Data.Graph.Indexed
import public Data.Graph.Indexed.Subgraph

%default total
%language ElabReflection

||| A shortest path of length `length` from a starting node to node `last`.
||| `combos` is the number of shortest paths of the same length leading
||| from `first` to `last`.
||| Node `first` is the first node after the root node, and is used to
||| check if two paths are disjoint.
public export
record Path (k : Nat) where
  constructor P
  ||| Number of nodes in the path (including the root node).
  length : Nat

  ||| The accumulated path viewed from the right
  path   : SnocList (Fin k)

  ||| True, if all nodes in the path are smaller than the root
  keep   : Bool

  ||| The first non-root node in the path
  first  : Fin k

  ||| The last node in the path
  last   : Fin k

  ||| Number of paths of the same length from `root` to
  ||| `last`. This is later used to compute the size of
  ||| a family of relevant cycles
  combos : Nat

0 Paths : Nat -> Type
Paths k = MArray k (Path k)

%runElab deriveIndexed "Path" [Show,Eq]

parameters {o    : Nat}
           (g    : ISubgraph o k e Nat)
           (root : Fin o)
           (rdeg : Nat)

  dummy : Path o
  dummy = P 0 [<] False root root 0

  -- `True` if node `n` is smaller than `root`. This is
  -- the ordering "pi" used in the paper.
  export %inline smaller : Fin o -> Bool
  smaller n =
    case compare (snd $ lab g n) rdeg of
      LT => True
      EQ => root < n
      GT => False

  -- Appends a node to a path. This also updates the `length` and `last` node.
  append : Path o -> Fin o -> Path o
  append (P l p k fs ls c) n =
    if fs == root
       then P (S l) (p :< n) (smaller n)      n  n c
       else P (S l) (p :< n) (k && smaller n) fs n c

  merge : Path o -> Fin o -> Path o -> Path o
  merge p n q =
    let True := S p.length == q.length | False => q
        True := p.keep                 | False => q
        True := q.keep                 | False => append p n
     in {combos $= (+ p.combos)} q

  adjNeighbours : Path o -> List (Fin o) -> Queue (Fin o) -> Paths o -@ CRes (Queue (Fin o)) (Paths o)
  adjNeighbours p []      qu m = qu # m
  adjNeighbours p (x::xs) qu m =
    let q # m2 := Core.get x m
        Z      := q.length | _ => adjNeighbours p xs qu (set x (merge p x q) m2)
        q2     := append p x
     in adjNeighbours p xs (enqueue qu x) (set x q2 m2)

  -- The `Queue` holds potential shortest paths in increasing
  -- length that still need to be processed.
  covering
  impl : SnocList (Path o) -> Queue (Fin o) -> Paths o -@ Ur (List $ Path o)
  impl sp q m =
    -- try and extract the current head from the queue
    case dequeue q of
      -- no more paths left. We are done
      Nothing     => discarding m $ MkBang (sp <>> [])
      -- We got a node to process and the tail of the queue
      Just (n,q2) =>
        let p # m2  := Core.get n m
            False   := p.length * 2 > o | True => discarding m2 $ MkBang (sp <>> [])
            q3 # m3 := adjNeighbours p (neighbours g n) q2 m2
         in impl (if p.keep then sp :< p else sp) q3 m3

  setRoot : Paths o -@ Paths o
  setRoot = set root (P 1 [<root] False root root 1)

  ||| Computes the shortest paths to all nodes reachable from
  ||| the given starting node.
  export
  shortestPaths : List (Path o)
  shortestPaths =
    let q := Queue.fromList [root]
     in unrestricted $ assert_total $ alloc o dummy (impl [<] q . setRoot)
