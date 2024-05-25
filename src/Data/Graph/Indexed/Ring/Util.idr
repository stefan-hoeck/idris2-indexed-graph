module Data.Graph.Indexed.Ring.Util

import Data.Graph.Indexed
import Data.SnocList

%default total

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
