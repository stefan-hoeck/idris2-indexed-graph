module Data.Graph.Ring.Util

import Data.SortedSet
import Data.Graph
import Data.SnocList

%default total

||| A set of unlabeled edges of order `k`
public export
0 EdgeSet : (g : Graph e n) -> Type
EdgeSet g = SortedSet (Edg g)

||| Adds an unlabeled edge to an edge set.
|||
||| The edge set is returned unmodified, if the two nodes are
||| identical.
export
addEdge : EdgeSet g -> Node g -> Node g -> EdgeSet g
addEdge es x y = maybe es (`insert` es) (mkEdg x y)

||| Adds an unlabeled edge to an edge set.
|||
||| The edge set is returned unmodified, if the two natural numbers
||| are not valid distinct nodes of order `k`.
export
addNatEdge : {g : _} -> EdgeSet g -> Nat -> Nat -> EdgeSet g
addNatEdge es x y =
  let Just fx := tryNatToFin x | Nothing => es
      Just fy := tryNatToFin y | Nothing => es
   in addEdge es (N fx) (N fy)

||| Converts a list of pairs of natural number to an edge set of
||| order `k`. Invalid pairs of nodes are silently dropped.
export
toEdgeSet : (g : _) -> List (Nat,Nat) -> EdgeSet g
toEdgeSet g = foldl (\es,(x,y) => addNatEdge es x y) empty

nodePairs : SnocList (a,a) -> List a -> SnocList (a,a)
nodePairs sp []     = sp
nodePairs sp (h::t) = nodePairs (sp <>< map (h,) t) t

||| True, if the given node is a member of a three-membered cycle.
|||
||| For sparse graphs, this check can be performed in linear time without
||| performing a proper ring detection, just be checking if two of the
||| neighbours of the given node are adjacent.
export
inThreeMemberedRing : {g : Graph e n} -> Node g -> Bool
inThreeMemberedRing x = any (uncurry adjacent) (nodePairs [<] (neighbours x))
