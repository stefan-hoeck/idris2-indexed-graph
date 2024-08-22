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

parameters (mq : MArray q (Maybe $ Fin t))
           (mt : MArray t (Maybe $ Fin q))

  -- Link a query node to a target node.
  assign : Fin q -> Fin t -> F1' [mq,mt]
  assign x y t =
    let _ # t := set mt y (Just x) t
     in set mq x (Just y) t

  -- Undo an assignment. We use this when backtracking
  -- from an assignment that didn't work.
  unassign : Fin q -> Fin t -> F1' [mq,mt]
  unassign x y t =
    let _ # t := set mt y Nothing t
     in set mq x Nothing t

--------------------------------------------------------------------------------
-- Linear Utilities
--------------------------------------------------------------------------------

parameters {k : _}
           (r : MArray k (Maybe a))
           {auto 0 p : Res r rs}

  -- Test if the value at the given position in a mutable array is still unset.
  %inline unset : Fin k -> F1 rs Bool
  unset x t = let m # t := get r x t in isNothing m # t

  -- Either extracts the target nodes from a successful query, or finds the
  -- first unassigned query node.
  findUnassigned : F1 rs (Either (Fin k) (Vect k a))
  findUnassigned t =
    let vs # t = toVectWith r (\x => maybe (Left x) Right) t
     in sequence vs # t

--------------------------------------------------------------------------------
-- Candidates
--------------------------------------------------------------------------------

-- A sorted list pairing query nodes with potential target nodes.
-- In case a query node is linked to an empty list, there are no
-- valid target nodes left, so we should abort and try something else.
0 Matrix : (q,t : Nat) -> Type
Matrix q t = AssocList q (List $ Fin t)

-- Remove the given node from all target node lists, because it has been
-- assigned to a query node.
%inline remove : Fin t -> Matrix q t -> Matrix q t
remove = map . filter . (/=)

-- Intersect two sorted lists of target nodes.
intersect : List (Fin t) -> List (Fin t) -> List (Fin t)
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
           {q,t : Nat}
           (mq      : MArray q (Maybe $ Fin t))
           (mt      : MArray t (Maybe $ Fin q))
           (me      : eq -> et -> Bool) -- edge label matcher
           (mn      : nq -> nt -> Bool) -- node label matcher
           (query   : IGraph q eq nq)   -- query node
           (target  : IGraph t et nt)   -- target node

  -- Computes a list of candidate mappings from lists of query nodes
  -- and target nodes (both the neighbours - plus edge labels - of the
  -- most recently assigned query and target node).
  --
  -- We have already veryfied, that both lists consist only of so far
  -- unassigned nodes.
  candidates : AssocList q eq -> AssocList t et -> Matrix q t
  candidates ps qs = mapKV cand ps
    where
      match : eq -> nq -> (Fin t, et) -> Maybe (Fin t)
      match veq vnq (y, vet) =
        if me veq vet && mn vnq (lab target y) then Just y else Nothing

      cand : Fin q -> eq -> List (Fin t)
      cand x lq = mapMaybe (match lq $ lab query x) (pairs qs)

  align : Fin q -> Fin t -> Matrix q t -> F1 [mq,mt] (Matrix q t)
  align x y m t =
    let nsX # t := filterLin (unset mq) (neighbours $ adj query x) t
        nsY # t := filterLin (unset mt) (neighbours $ adj target y) t
     in unionWith intersect (remove y m) (candidates nsX nsY) # t

  covering
  tryAll : Matrix q t -> F1 [mq,mt] Bool

  covering
  try : Fin q -> List (Fin t) -> Matrix q t -> F1 [mq,mt] Bool

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
      Just (x,vs) => try x vs (delete x m) t

  -- Tries to align all connected components of the query graph
  -- with nodes of the target graph.
  covering
  run : F1 [mq,mt] (Maybe $ Vect q (Fin t))
  run t = -- (S m1 a1) =
    let Left x # t := findUnassigned mq t | Right arr # t => Just arr # t
        ns     # t := filter1 (unset mt) (nodes target) t
        ns'        := filter (\y => mn (lab query x) (lab target y)) ns
        True   # t := try x ns' empty t | False # t => Nothing # t
     in run t

||| Using the given matching functions for node and edge labels, this
||| tries to align the `query` graph with the `target` graph in such
||| a way, that each query node is linked to a single target node.
export covering
query :
     {0 eq,et,nq,nt : Type}
  -> {q,t : Nat}
  -> (me      : eq -> et -> Bool) -- edge label matcher
  -> (mn      : nq -> nt -> Bool) -- node label matcher
  -> (query   : IGraph q eq nq)   -- query node
  -> (target  : IGraph t et nt)   -- target node
  -> Maybe (Vect q (Fin t))
query me mn que tgt =
  run1 $ \tk =>
    let A mt tk  := newMArray t Nothing tk
        A mq tk  := newMArray q Nothing tk
        res # tk := run mq mt me mn que tgt tk
        _   # tk := release mt tk
        _   # tk := release mq tk
     in res # tk
