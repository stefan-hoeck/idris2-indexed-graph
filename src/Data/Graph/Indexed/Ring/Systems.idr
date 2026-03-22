||| Computes the ring systems (biconnected components) of
||| a graph and provides an efficient mapping assigning
||| each node to the ring system it belongs to.
module Data.Graph.Indexed.Ring.Systems

import Data.Array
import Data.Graph.Indexed
import Data.Graph.Indexed.Subgraph
import Data.Linear.Traverse1

%default total

||| Organizes a graph into a system of biconnected components,
||| allowing us to figure out if a node or edge is cyclic,
||| as well as get the cyclic subgraph each node or edge
||| belongs to.
|||
||| All lookup functions operate in constant time.
public export
record RingSystems (k : Nat) (e,n : Type) where
  constructor RS
  graph   : IGraph k e n
  systems : Nat
  rings   : IArray systems (Subgraph k e n)
  ringMap : IArray k (Fin (S systems))

||| True, if the given node is part of a ring systems.
export
isInRing : RingSystems k e n -> Fin k -> Bool
isInRing rs x =
  case rs.ringMap `at` x of
    FZ => False
    _  => True

||| True, if the two nodes are part of the same ring system.
export
inSameRing : RingSystems k e n -> (x,y : Fin k) -> Bool
inSameRing rs x y = isInRing rs x && at rs.ringMap x == at rs.ringMap y

||| Returns the cyclic subgraph a node belongs to.
|||
||| Returns `Nothing` if a node is not part of a cycle.
export
ringFor : RingSystems k e n -> Fin k -> Maybe (Subgraph k e n)
ringFor rs x =
  case rs.ringMap `at` x of
    FZ   => Nothing
    FS k => Just $ rs.rings `at` k

||| Computes the biconnected components and corresponding node mappings
||| from an indexed graph.
export
ringSystems : {k : _} -> IGraph k e n -> RingSystems k e n
ringSystems g =
 let bcs := biconnectedComponents g
  in RS g _ (arrayL bcs) (fromPairs k FZ $ zipWithIndex bcs >>= pairs)

  where
    pairs : {y : _} -> (Nat,Graph e (Fin k, n)) -> List (Nat, Fin y)
    pairs (n,G _ g) =
     let Just x := tryNatToFin (S n) | Nothing => []
      in (\l => (finToNat $ fst l, x)) <$> labels g
