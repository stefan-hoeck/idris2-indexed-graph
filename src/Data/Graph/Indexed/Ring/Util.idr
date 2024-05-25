module Data.Graph.Indexed.Ring.Util

import Data.SortedSet
import Data.Graph.Indexed
import Data.SnocList

%default total

||| A set of unlabeled edges of order `k`
public export
0 EdgeSet : (k : Nat) -> Type
EdgeSet k = SortedSet (Edge k ())

||| Adds an unlabeled edge to an edge set.
|||
||| The edge set is returned unmodified, if the two nodes are
||| identical.
export
addEdge : EdgeSet k -> Fin k -> Fin k -> EdgeSet k
addEdge es x y = maybe es (`insert` es) (mkEdge x y ())

||| Adds an unlabeled edge to an edge set.
|||
||| The edge set is returned unmodified, if the two natural numbers
||| are not valid distinct nodes of order `k`.
export
addNatEdge : {k : _} -> EdgeSet k -> Nat -> Nat -> EdgeSet k
addNatEdge es x y =
  let Just fx := tryNatToFin x | Nothing => es
      Just fy := tryNatToFin y | Nothing => es
   in addEdge es fx fy

||| Converts a list of pairs of natural number to an edge set of
||| order `k`. Invalid pairs of nodes are silently dropped.
export
toEdgeSet : {k : _} -> List (Nat,Nat) -> EdgeSet k
toEdgeSet = foldl (\es,(x,y) => addNatEdge es x y) empty

nodePairs : SnocList (a,a) -> List a -> SnocList (a,a)
nodePairs sp []     = sp
nodePairs sp (h::t) = nodePairs (sp <>< map (h,) t) t

||| True, if the given node is a member of a three-membered cycle.
|||
||| For sparse graphs, this check can be performed in linear time without
||| performing a proper ring detection, just be checking if two of the
||| neighbours of the given node are adjacent.
export
inThreeMemberedRing : IGraph k e n -> Fin k -> Bool
inThreeMemberedRing g x =
  any (\(a,b) => adjacent g a b) (nodePairs [<] (neighbours g x))
