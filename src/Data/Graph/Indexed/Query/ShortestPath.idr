module Data.Graph.Indexed.Query.ShortestPath

import Data.Array.Mutable
import Data.Linear.Ref1
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

%runElab deriveIndexed "Path" [Show,Eq]

parameters {o    : Nat}
           (g    : ISubgraph o k e Nat)
           (root : Fin o)
           (rdeg : Nat)
           (q    : Ref s (Queue $ Fin o))
           (r    : MArray s o (Path o))

  %inline
  deq : F1 s (Maybe $ Fin o)
  deq t =
   let qu # t := read1 q t
    in case dequeue qu of
         Nothing     => Nothing # t
         Just (v,q2) => let _ # t := write1 q q2 t in Just v # t

  %inline
  enq : Fin o -> F1' s
  enq v t = let qu # t := read1 q t in write1 q (enqueue qu v) t

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

  adjNeighbours : Path o -> List (Fin o) -> F1' s
  adjNeighbours p []      t = () # t
  adjNeighbours p (x::xs) t =
    let p2 # t := Core.get r x t
        Z      := p2.length
          | _ => let _ # t := set r x (merge p x p2) t in adjNeighbours p xs t
        _ # t  := set r x (append p x) t
        _ # t  := mod1 q (`enqueue` x) t
     in adjNeighbours p xs t

  covering
  impl : SnocList (Path o) -> F1 s (List $ Path o)
  impl sp t =
    case deq t of
      Nothing # t => (sp <>> []) # t
      Just n  # t =>
       let p # t   := Core.get r n t
           False   := p.length * 2 > o | True => (sp <>> []) # t
           _ # t   := adjNeighbours p (neighbours g n) t
        in impl (if p.keep then sp :< p else sp) t

||| Computes the shortest paths to all nodes reachable from
||| the given starting node.
export
shortestPaths : {o : _} -> ISubgraph o k e Nat -> Fin o -> List (Path o)
shortestPaths g root =
  assert_total $ run1 $ \t =>
    let r # t := marray1 o (P 0 [<] False root root 0) t
        q # t := ref1 (Queue.fromList [root]) t
        _ # t := set r root (P 1 [<root] False root root 1) t
     in impl g root (deg g root) q r [<] t
