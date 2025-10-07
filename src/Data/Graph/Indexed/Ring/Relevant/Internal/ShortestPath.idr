||| This module is provides utilities used to compute families of relevant cycles
||| as described by Vismara et al in "Union of all the minimum cycle bases of a graph"
||| (The Electronic Journal of Combinatorics 4 (1997)).
module Data.Graph.Indexed.Ring.Relevant.Internal.ShortestPath

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
  |||
  ||| This flag is used for efficiency, as it allows us to avoid
  ||| computing the same cycle more than once.
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

  -- dequeue a value from the mutable queue
  %inline
  deq : F1 s (Maybe $ Fin o)
  deq t =
   let qu # t := read1 q t
    in case dequeue qu of
         Nothing     => Nothing # t
         Just (v,q2) => let _ # t := write1 q q2 t in Just v # t

  -- enqueue a value at the mutable queue
  %inline
  enq : Fin o -> F1' s
  enq v t = let qu # t := read1 q t in write1 q (enqueue qu v) t

  -- `True` if node `n` is "smaller" than `root`. This is
  -- the ordering "pi" used in the paper.
  %inline smaller : Fin o -> Bool
  smaller n =
    case compare (snd $ lab g n) rdeg of
      LT => True
      EQ => root < n
      GT => False

  -- Appends a node to a path. This also updates the `length` and `last` node.
  append : Path o -> Fin o -> Path o
  append (P l p k fs ls c) n =
    -- initially, a `Path` has set its `first` node to `root`.
    -- If that's the case, we are at first node after root.
    -- Note: Paths are only to be kept, if all their nodes are
    -- `smaller` than the root node.
    if fs == root
       then P (S l) (p :< n) (smaller n)      n  n c
       else P (S l) (p :< n) (k && smaller n) fs n c

  -- two paths from `root` to `n` are to be combined, if
  -- they are of the same length and both are to be kept.
  -- `n` will be appended to `p`. `q` already has `n` as its
  -- last node.
  merge : Path o -> Fin o -> Path o -> Path o
  merge p n q =
    let True := S p.length == q.length | False => q
        True := p.keep                 | False => q
        True := q.keep                 | False => append p n
     in {combos $= (+ p.combos)} q

  -- process the neighbours of the last node of the given path
  adjNeighbours : Path o -> List (Fin o) -> F1' s
  adjNeighbours p []      t = () # t
  adjNeighbours p (x::xs) t =
    let p2 # t := Core.get r x t
     in case p2.length of
          -- `x` has not yet ben processed. append it to `p` and enqeueue it.
          Z =>
           let _ # t  := set r x (append p x) t
               _ # t  := enq x t
            in adjNeighbours p xs t
          -- `x` has been processed. merge the two paths but don't enqueue it
          _ =>
           let _ # t := set r x (merge p x p2) t
            in adjNeighbours p xs t

  covering
  impl : SnocList (Path o) -> F1 s (List $ Path o)
  impl sp t =
    -- process the next enqueued node and the path associated with it
    case deq t of
      Nothing # t => (sp <>> []) # t
      Just n  # t =>
       let p # t := Core.get r n t
           False := p.length * 2 > o | True => (sp <>> []) # t -- abort early
           _ # t := adjNeighbours p (neighbours g n) t
        in impl (if p.keep then sp :< p else sp) t

||| Converts a subgraph to hold the degree of each node as its label.
export
toDegs : Subgraph k e n -> Subgraph k e Nat
toDegs (G o g) = G o $ mapAdj (\(A (x,_) ns) => A (x, length ns) ns) g

||| Computes the shortest paths to all nodes reachable from
||| the given starting node.
|||
||| Note: This is not a general shortest paths algorithm but a utility
||| for computing relevant cycles. Since paths are later merged to cycles,
||| only paths of length up to half the graph order are computed.
export
shortestPaths : {o : _} -> ISubgraph o k e Nat -> Fin o -> List (Path o)
shortestPaths g root =
  assert_total $ run1 $ \t =>
    let r # t := marray1 o (P 0 [<] False root root 0) t
        q # t := ref1 (Queue.fromList [root]) t
        _ # t := set r root (P 1 [<root] False root root 1) t
     in impl g root (snd $ lab g root) q r [<] t
