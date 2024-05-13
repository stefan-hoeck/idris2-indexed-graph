||| This is an implementation of a simple but efficient subgraph isomorphism
||| algorithm.
module Data.Graph.Indexed.Query.Subgraph

import Data.AssocList.Indexed
import Data.Array.Mutable
import Data.Graph.Indexed
import Data.Vect

%default total

--------------------------------------------------------------------------------
-- Local mutable State
--------------------------------------------------------------------------------

-- When running a query, we use two mutable arrays to associate
-- query nodes with target nodes and vice versa.
record ST (q,t : Nat) where
  constructor S
  1 mapped   : MArray q (Maybe $ Fin t)
  1 assigned : MArray t (Maybe $ Fin q)

-- Cleanup once we are done.
discardST : a -> ST q t -@ Ur a
discardST x (S m a) =
  let () := discarding m ()
      () := discarding a ()
   in MkBang x

-- Link a query node to a target node.
assign : Fin q -> Fin t -> ST q t -@ ST q t
assign x y (S mp as) =
  let mp2 := set x (Just y) mp
      as2 := set y (Just x) as
   in S mp2 as2

-- Undo an assignment. We use this when backtracking
-- from an assignment that didn't work.
unassign : Fin q -> Fin t -> ST q t -@ ST q t
unassign x y (S mp as) =
  let mp2 := set x Nothing mp
      as2 := set y Nothing as
   in S mp2 as2

--------------------------------------------------------------------------------
-- Linear Utilities
--------------------------------------------------------------------------------

0 Fun1 : Nat -> Type -> Type -> Type
Fun1 k s t = MArray k t -@ CRes s (MArray k t)

-- Test if the value at the given position in a mutable array is still unset.
%inline unset : Fin k -> Fun1 k Bool (Maybe a)
unset v arr = let m # arr2 := get v arr in isNothing m # arr2

-- Either extracts the target nodes from a successful query, or finds the
-- first unassigned query node.
findUnassigned : {k : _} -> Fun1 k (Either (Fin k) (Vect k a)) (Maybe a)
findUnassigned m =
  let vs # m2 = toVectWith (\x => maybe (Left x) Right) m
   in sequence vs # m2

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
           (me     : eq -> et -> Bool) -- edge label matcher
           (mn     : nq -> nt -> Bool) -- node label matcher
           (query  : IGraph q eq nq)   -- query node
           (target : IGraph t et nt)   -- target node

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

  align : Fin q -> Fin t -> Matrix q t -> ST q t -@ CRes (Matrix q t) (ST q t)
  align x y m (S m1 a1) =
    let nsX # m2 := Indexed.filterLin unset (neighbours $ adj query x) m1
        nsY # a2 := Indexed.filterLin unset (neighbours $ adj target y) a1
     in unionWith intersect (remove y m) (candidates nsX nsY) # S m2 a2

  covering
  tryAll : Matrix q t -> ST q t -@ CRes Bool (ST q t)

  covering
  try : Fin q -> List (Fin t) -> Matrix q t -> ST q t -@ CRes Bool (ST q t)

  -- There are no valid mappings left for query node `x`, so we abort
  -- with `False`.
  try x []      cs st = False # st

  try x (v::vs) cs st =
    let st2 := assign x v st -- map query node `x` to target node `v`

        -- Align the neighbours of x and v and update the candidate matrix.
        cs2 # st3   := align x v cs st2 --

        -- Iterate over the matrix of candidates to assign the
        -- remaining query nodes to target nodes. If this fails,
        -- undo the the mapping from `x` to `v` and try another
        -- one from `vs`.
        False # st3 := tryAll cs2 st3 | res => res
     in try x vs cs (unassign x v st3)

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
  run : ST q t -@ Ur (Maybe $ Vect q (Fin t))
  run (S m1 a1) =
    let Left x # m2 := findUnassigned m1
          | Right arr # m2 => discardST (Just arr) (S m2 a1)
        ns # a2 := Mutable.filterLin unset (nodes target) a1
        ns'     := filter (\y => mn (lab query x) (lab target y)) ns
        True # s2 := try x ns' empty (S m2 a2)
          | False # s2 => discardST Nothing s2
     in run s2

  ||| Using the given matching functions for node and edge labels, this
  ||| tries to align the `query` graph with the `target` graph in such
  ||| a way, that each query node is linked to a single target node.
  export covering
  query : Maybe (Vect q (Fin t))
  query = unrestricted $ alloc q Nothing $ \mq => alloc t Nothing (run . S mq)
