||| Computes the ring systems (biconnected components) of
||| a graph and provides an efficient mapping assigning
||| each node to the ring system it belongs to.
module Data.Graph.Ring.Systems

import Data.Array
import Data.Graph
import Data.Graph.Subgraph
import Data.Linear.Traverse1

%default total

||| Organizes a graph into a system of biconnected components,
||| allowing us to figure out if a node or edge is cyclic,
||| as well as get the cyclic subgraph each node or edge
||| belongs to.
|||
||| All lookup functions operate in constant time.
public export
record RingSystems (g : Graph e n) where
  constructor RS
  systems : Nat
  rings   : IArray systems (Subgraph g)
  ringMap : IArray g.order (Fin (S systems))

||| True, if the given node is part of a ring systems.
export
isInRing : RingSystems g -> Node g -> Bool
isInRing rs x =
  case rs.ringMap `atN` x of
    FZ => False
    _  => True

||| True, if the two nodes are part of the same ring system.
export
inSameRing : RingSystems g -> (x,y : Node g) -> Bool
inSameRing rs x y = isInRing rs x && atN rs.ringMap x == atN rs.ringMap y

||| Returns the cyclic subgraph a node belongs to.
|||
||| Returns `Nothing` if a node is not part of a cycle.
export
ringFor : RingSystems g -> Node g -> Maybe (Subgraph g)
ringFor rs x =
  case rs.ringMap `atN` x of
    FZ   => Nothing
    FS k => Just $ rs.rings `at` k

||| Computes the biconnected components and corresponding node mappings
||| from an indexed graph.
export
ringSystems : (g : Graph e n) -> RingSystems g
ringSystems g =
 let bcs := biconnectedComponents g
  in RS _ (arrayL bcs) (fromPairs g.order FZ $ zipWithIndex bcs >>= pairs)

  where
    pairs : {y : _} -> (Nat,Subgraph g) -> List (Nat, Fin y)
    pairs (n,g) =
     let Just x := tryNatToFin (S n) | Nothing => []
      in (\l => (cast l, x)) <$> labels g
