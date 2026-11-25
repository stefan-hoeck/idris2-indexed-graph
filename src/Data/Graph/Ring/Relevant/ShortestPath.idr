||| This module provides utilities used to compute families of relevant cycles
||| as described by Vismara et al in "Union of all the minimum cycle bases of a graph"
||| (The Electronic Journal of Combinatorics 4 (1997)).
|||
||| In particular, it computes the number of shortest paths between a root
||| node and all other nodes in a graph.
|||
||| Please note that this is internal stuff. The algorithm is not suitable
||| as a general shortest path algorithm, as it computes only paths up
||| to half the graph order in length.
module Data.Graph.Ring.Relevant.ShortestPath

import Data.Array.Mutable
import Data.Graph.Ring.Relevant.Types
import Data.Linear.Ref1
import Data.List
import Data.Queue
import public Data.Graph
import public Data.Graph.Subgraph

%default total

||| `True` if node `n` is "smaller" than `root`. This is
||| the ordering "pi" used in the paper.
export %inline
smaller : Node g -> IArray g.order Nat -> Node g -> Bool
smaller root degs n =
  case compare (atN degs n) (atN degs root) of
    LT => True
    EQ => root < n
    GT => False

parameters (g    : Graph e n)
           (root : Node g)
           (degs : IArray g.order Nat)
           (q    : Ref s (Queue $ Node g))
           (r    : MArray s g.order (Path g))

  -- dequeue a value from the mutable queue
  %inline
  deq : F1 s (Maybe $ Node g)
  deq t =
   let qu # t := read1 q t
    in case dequeue qu of
         Nothing     => Nothing # t
         Just (v,q2) => let _ # t := write1 q q2 t in Just v # t

  -- enqueue a value at the mutable queue
  %inline
  enq : Node g -> F1' s
  enq v t = let qu # t := read1 q t in write1 q (enqueue qu v) t

  -- Appends a node to a path. This also updates the `length` and `last` node.
  append : Path g -> Node g -> Path g
  append (P l p k fs ls c) n =
    -- initially, a `Path` has set its `first` node to `root`.
    -- If that's the case, we are at first node after root.
    -- Note: Paths are only to be kept, if all their nodes are
    -- `smaller` than the root node.
    if fs == root
       then P (S l) (p :< n) (smaller root degs n)      n  n c
       else P (S l) (p :< n) (k && smaller root degs n) fs n c

  -- two paths from `root` to `n` are to be combined, if
  -- they are of the same length and both are to be kept.
  -- `n` will be appended to `p`. `q` already has `n` as its
  -- last node.
  merge : Path g -> Node g -> Path g -> Path g
  merge p n q =
    let True := S p.length == q.length | False => q
        True := p.keep                 | False => q
        True := q.keep                 | False => append p n
     in {combos $= (+ p.combos)} q

  -- process the neighbours of the last node of the given path
  adjNeighbours : Path g -> List (Node g) -> F1' s
  adjNeighbours p []      t = () # t
  adjNeighbours p (x::xs) t =
    let p2 # t := Core.get r x.node t
     in case p2.length of
          -- `x` has not yet ben processed. append it to `p` and enqeueue it.
          Z =>
           let _ # t  := set r x.node (append p x) t
               _ # t  := enq x t
            in adjNeighbours p xs t
          -- `x` has been processed. merge the two paths but don't enqueue it
          _ =>
           let _ # t := set r x.node (merge p x p2) t
            in adjNeighbours p xs t

  covering
  impl : SnocList (Path g) -> F1 s (List $ Path g)
  impl sp t =
    -- process the next enqueued node and the path associated with it
    case deq t of
      Nothing # t => (sp <>> []) # t
      Just n  # t =>
       let p # t := Core.get r n.node t
           False := p.length * 2 > g.order | True => (sp <>> []) # t -- abort early
           _ # t := adjNeighbours p (neighbours n) t
        in impl (if p.keep then sp :< p else sp) t

||| Computes the shortest paths to all nodes reachable from
||| the given starting node.
|||
||| Note: This is not a general shortest paths algorithm but a utility
||| for computing relevant cycles. Since paths are later merged to cycles,
||| only paths of length up to half the graph order are computed.
export
shortestPaths : (g : Graph e n) -> IArray g.order Nat -> Node g -> List (Path g)
shortestPaths g degs root =
  assert_total $ run1 $ \t =>
    let r # t := marray1 g.order (P 0 [<] False root root 0) t
        q # t := ref1 (Queue.fromList [root]) t
        _ # t := set r root.node (P 1 [<root] False root root 1) t
     in impl g root degs q r [<] t
