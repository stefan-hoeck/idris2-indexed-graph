||| This is an implementation of a simple but efficient subgraph isomorphism
||| algorithm.
module Data.Graph.Indexed.Query.Subgraph

import Data.Array.Mutable
import Data.AssocList.Indexed
import Data.Graph.Indexed
import Data.Linear.List
import Data.Vect

%default total

--------------------------------------------------------------------------------
-- Local mutable State
--------------------------------------------------------------------------------

data Tag = Q | T

parameters (mq : MArray s q.order (Maybe $ Node t))
           (mt : MArray s t.order (Maybe $ Node q))

  -- Link a query node to a target node.
  assign : Node q -> Node t -> F1' s
  assign x y t =
    let _ # t := set mt y.node (Just x) t
     in set mq x.node (Just y) t

  -- Undo an assignment. We use this when backtracking
  -- from an assignment that didn't work.
  unassign : Node q -> Node t -> F1' s
  unassign x y t =
    let _ # t := set mt y.node Nothing t
     in set mq x.node Nothing t

--------------------------------------------------------------------------------
-- Linear Utilities
--------------------------------------------------------------------------------

parameters {k : _}
           (r : MArray s k (Maybe a))

  -- Test if the value at the given position in a mutable array is still unset.
  %inline unset : Fin k -> F1 s Bool
  unset x t = let m # t := get r x t in isNothing m # t

  -- Either extracts the target nodes from a successful query, or finds the
  -- first unassigned query node.
  findUnassigned : F1 s (Either (Fin k) (Vect k a))
  findUnassigned t =
    let vs # t = toVectWith r (\x => maybe (Left x) Right) t
     in sequence vs # t

--------------------------------------------------------------------------------
-- Candidates
--------------------------------------------------------------------------------

-- A sorted list pairing query nodes with potential target nodes.
-- In case a query node is linked to an empty list, there are no
-- valid target nodes left, so we should abort and try something else.
0 Matrix : (q : Graph eq nq) -> (t : Graph et nt) -> Type
Matrix q t = AssocList q.order (List $ Node t)

-- Remove the given node from all target node lists, because it has been
-- assigned to a query node.
%inline remove : Node t -> Matrix q t -> Matrix q t
remove = map . filter . (/=)

-- Intersect two sorted lists of target nodes.
intersect : List (Node t) -> List (Node t) -> List (Node t)
intersect l@(x::xs) r@(y::ys) =
  case compare x y of
    LT => intersect xs r
    EQ => x :: intersect xs ys
    GT => intersect l ys
intersect _ _ = []

--------------------------------------------------------------------------------
-- Algorithm
--------------------------------------------------------------------------------

parameters {0 eq,et,nq,nt : Type}
           (q  : Graph eq nq) -- query graph
           (t  : Graph et nt) -- target graph
           (mq : MArray s q.order (Maybe $ Node t))
           (mt : MArray s t.order (Maybe $ Node q))
           (me : eq -> et -> Bool) -- edge label matcher
           (mn : nq -> nt -> Bool) -- node label matcher

  -- Computes a list of candidate mappings from lists of query nodes
  -- and target nodes (both the neighbours - plus edge labels - of the
  -- most recently assigned query and target node).
  --
  -- We have already veryfied, that both lists consist only of so far
  -- unassigned nodes.
  candidates : AssocList q.order eq -> AssocList t.order et -> Matrix q t
  candidates ps qs = mapKV (\x,v => cand (N x) v) ps
    where
      match : eq -> nq -> (Node t, et) -> Maybe (Node t)
      match veq vnq (y, vet) =
        if me veq vet && mn vnq (lab y) then Just y else Nothing

      cand : Node q -> eq -> List (Node t)
      cand x lq = mapMaybe (match lq $ lab x) (fromPairs $ pairs qs)

  align : Node q -> Node t -> Matrix q t -> F1 s (Matrix q t)
  align x y m t =
    let nsX # t := filterLin (unset mq) (neighbours $ adj x) t
        nsY # t := filterLin (unset mt) (neighbours $ adj y) t
     in unionWith intersect (remove y m) (candidates nsX nsY) # t

  covering
  tryAll : Matrix q t -> F1 s Bool

  covering
  try : Node q -> Nodes t -> Matrix q t -> F1 s Bool

  -- There are no valid mappings left for query node `x`, so we abort
  -- with `False`.
  try x []      cs t = False # t

  try x (v::vs) cs t =
    let _ # t := assign mq mt x v t -- map query node `x` to target node `v`

        -- Align the neighbours of x and v and update the candidate matrix.
        cs2 # t   := align x v cs t --

        -- Iterate over the matrix of candidates to assign the
        -- remaining query nodes to target nodes. If this fails,
        -- undo the the mapping from `x` to `v` and try another
        -- one from `vs`.
        False # t := tryAll cs2 t | res => res
        _ # t := unassign mq mt x v t
     in try x vs cs t

  -- This extracts the query node with the lowest number of
  -- candidate nodes from the target. If there is no node left,
  -- we are done with the current connected component.
  tryAll m t =
    case minBy length m of
      Nothing     => True # t
      Just (x,vs) => try (N x) vs (delete x m) t

  -- Tries to align all connected components of the query graph
  -- with nodes of the target graph.
  covering
  run : F1 s (Maybe $ Vect q.order (Node t))
  run y = -- (S m1 a1) =
    let Left x # y := findUnassigned mq y | Right arr # y => Just arr # y
        ns     # y := filter1 (unset mt . node) (nodes t) y
        ns'        := List.filter (\y => mn (lab $ N x) (lab y)) ns
        True   # y := try (N x) ns' empty y | False # y => Nothing # y
     in run y

||| Using the given matching functions for node and edge labels, this
||| tries to align the `query` graph with the `target` graph in such
||| a way, that each query node is linked to a single target node.
export covering
query :
     {0 eq,et,nq,nt : Type}
  -> (me      : eq -> et -> Bool) -- edge label matcher
  -> (mn      : nq -> nt -> Bool) -- node label matcher
  -> (query   : Graph eq nq)   -- query node
  -> (target  : Graph et nt)   -- target node
  -> Maybe (Vect query.order (Node target))
query me mn que tgt =
  run1 $ \tk =>
    let mt # tk := marray1 tgt.order Nothing tk
        mq # tk := marray1 que.order Nothing tk
     in run que tgt mq mt me mn tk
