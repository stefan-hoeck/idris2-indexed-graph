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

parameters {auto mq : MArray Q s q (Maybe $ Fin t)}
           {auto mt : MArray T s t (Maybe $ Fin q)}

  -- Link a query node to a target node.
  assign : Fin q -> Fin t -> F1' s
  assign x y t = Core.setAt Q x (Just y) (Core.setAt T y (Just x) t)

  -- Undo an assignment. We use this when backtracking
  -- from an assignment that didn't work.
  unassign : Fin q -> Fin t -> F1' s
  unassign x y t = Core.setAt Q x Nothing (Core.setAt T y Nothing t)

--------------------------------------------------------------------------------
-- Linear Utilities
--------------------------------------------------------------------------------

-- Test if the value at the given position in a mutable array is still unset.
%inline unset : (0 tag : _) -> MArray tag s k (Maybe a) => Fin k -> F1 s Bool
unset tag x t = let m # t2 := Core.getAt tag x t in isNothing m # t2

-- Either extracts the target nodes from a successful query, or finds the
-- first unassigned query node.
findUnassigned :
     {k : _}
  -> (0 tag : _)
  -> {auto arr : MArray tag s k (Maybe a)}
  -> F1 s (Either (Fin k) (Vect k a))
findUnassigned tag t =
  let vs # t2 = toVectWith tag (\x => maybe (Left x) Right) t
   in sequence vs # t2
--
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
           {auto mq : MArray Q s q (Maybe $ Fin t)}
           {auto mt : MArray T s t (Maybe $ Fin q)}
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

  align : Fin q -> Fin t -> Matrix q t -> F1 s (Matrix q t)
  align x y m t =
    let nsX # t2 := filterLin (unset Q) (neighbours $ adj query x) t
        nsY # t3 := filterLin (unset T) (neighbours $ adj target y) t2
     in unionWith intersect (remove y m) (candidates nsX nsY) # t3

  covering
  tryAll : Matrix q t -> F1 s Bool

  covering
  try : Fin q -> List (Fin t) -> Matrix q t -> F1 s Bool

  -- There are no valid mappings left for query node `x`, so we abort
  -- with `False`.
  try x []      cs t = False # t

  try x (v::vs) cs t =
    let t2 := assign x v t -- map query node `x` to target node `v`

        -- Align the neighbours of x and v and update the candidate matrix.
        cs2 # t3   := align x v cs t2 --

        -- Iterate over the matrix of candidates to assign the
        -- remaining query nodes to target nodes. If this fails,
        -- undo the the mapping from `x` to `v` and try another
        -- one from `vs`.
        False # t4 := tryAll cs2 t3 | res => res
     in try x vs cs (unassign x v t4)

  -- This extracts the query node with the lowest number of
  -- candidate nodes from the target. If there is no node left,
  -- we are done with the current connected component.
  tryAll m st =
    case minBy length m of
      Nothing     => True # st
      Just (x,vs) => try x vs (delete x m) st

  -- Tries to align all connected components of the query graph
  -- with nodes of the target graph.
  covering
  run : F1 s (Maybe $ Vect q (Fin t))
  run t = -- (S m1 a1) =
    let Left x # t2 := findUnassigned Q t | Right arr # t2 => Just arr # t2
        ns # t3 := filter1 (unset T) (nodes target) t2
        ns'     := filter (\y => mn (lab query x) (lab target y)) ns
        True # t4 := try x ns' empty t3 | False # t4 => Nothing # t4
     in run t4

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
  run1 $ \t1 =>
    let aq # t2 := newMArrayAt Q q (the (Maybe $ Fin t) Nothing) t1
        at # t3 := newMArrayAt T t (the (Maybe $ Fin q) Nothing) t2
     in run me mn que tgt t3
